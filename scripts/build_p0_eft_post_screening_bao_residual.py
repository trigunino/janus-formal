from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_hubble_budget_stress_test import score_variant
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_hubble_budget_stress_test import score_variant
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_post_screening_bao_residual.md")
JSON_PATH = Path("outputs/reports/p0_eft_post_screening_bao_residual.json")


def run_scan() -> dict:
    constants, radion = master_branch_background(z_max=2.5)
    rows = []
    omega_grid = [0.20, 0.24, 0.27, 0.30, 0.315, 0.33, constants["Omega_m0"]]
    # score_variant always fits the global BAO scale analytically. That scale is the
    # effective ruler_scale diagnostic; the redshift-shape quality is in chi2.
    for omega_m in omega_grid:
        row = score_variant(
            f"post_screening_omega_m_{omega_m:g}",
            constants,
            radion,
            {"spin_coeff": 0.0, "Omega_m0": omega_m, "spin_background_projection": 0.0},
        )
        row["Omega_m_bg"] = omega_m
        row["xi_bg"] = 0.0
        row["ruler_scale_fit"] = row["scale"]
        rows.append(row)
    valid = [row for row in rows if row["valid"]]
    best = min(valid, key=lambda row: row["chi2"])
    fixed_growth_matter = next(row for row in valid if abs(row["Omega_m_bg"] - constants["Omega_m0"]) < 1e-12)
    return {
        "description": "Post-screening BAO residual scan with xi_bg=0.",
        "status": "post-screening-bao-residual-scan-computed",
        "growth_branch_Omega_m0": constants["Omega_m0"],
        "xi_bg": 0.0,
        "xi_growth": 1.0,
        "rows": rows,
        "best": best,
        "fixed_growth_matter_score": fixed_growth_matter,
        "shape_rescued_by_omega_m_and_ruler": best["chi2"] < 30.0,
        "omega_m_tension_with_growth": abs(best["Omega_m_bg"] - constants["Omega_m0"]),
        "verdict": (
            "If best chi2 is acceptable only far from the growth Omega_m0, the remaining BAO "
            "problem is a background/growth matter split or missing ruler map, not spin background leakage."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Post-Screening BAO Residual",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Growth branch Omega_m0: {payload['growth_branch_Omega_m0']}",
        f"xi_bg: {payload['xi_bg']}",
        f"xi_growth: {payload['xi_growth']}",
        f"Shape rescued by Omega_m/ruler scan: {payload['shape_rescued_by_omega_m_and_ruler']}",
        f"Omega_m tension with growth: {payload['omega_m_tension_with_growth']:.6g}",
        "",
        "## Scan",
        "",
        "| Omega_m_bg | chi2 | chi2/dof | DH chi2 | DM chi2 | DV chi2 | ruler scale |",
        "|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['Omega_m_bg']:.6g} | {row['chi2']:.6g} | {row['reduced_chi2']:.6g} | "
            f"{row['DH_diag_chi2']:.6g} | {row['DM_diag_chi2']:.6g} | "
            f"{row['DV_diag_chi2']:.6g} | {row['ruler_scale_fit']:.6g} |"
        )
    best = payload["best"]
    lines.extend(
        [
            "",
            "## Best",
            "",
            f"- Omega_m_bg: {best['Omega_m_bg']}",
            f"- chi2: {best['chi2']:.6g}",
            f"- chi2/dof: {best['reduced_chi2']:.6g}",
            f"- ruler scale: {best['ruler_scale_fit']:.6g}",
            "",
            "## Verdict",
            "",
            payload["verdict"],
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = run_scan()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
