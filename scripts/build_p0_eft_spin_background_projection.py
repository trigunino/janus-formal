from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_hubble_budget_stress_test import score_variant
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_hubble_budget_stress_test import score_variant
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_spin_background_projection.md")
JSON_PATH = Path("outputs/reports/p0_eft_spin_background_projection.json")


def classify_best_xi(best: dict) -> str:
    xi = best["xi_bg"]
    if xi == 0.0 and best["chi2"] < 100.0:
        return "scenario_A_spin_strictly_perturbative"
    if 0.0 < xi < 0.25 and best["chi2"] < 100.0:
        return "scenario_B_spin_partially_homogenized"
    return "scenario_C_projection_not_sufficient"


def run_projection_scan() -> dict:
    constants, radion = master_branch_background(z_max=2.5)
    base_spin = constants["spin_coeff"]
    rows = []
    for index in range(21):
        xi_bg = round(index / 20.0, 3)
        row = score_variant(
            f"xi_bg_{xi_bg:g}",
            constants,
            radion,
            {"spin_coeff": base_spin * xi_bg, "spin_background_projection": xi_bg},
        )
        row["xi_bg"] = xi_bg
        row["xi_growth"] = 1.0
        rows.append(row)
    valid = [row for row in rows if row["valid"]]
    best = min(valid, key=lambda row: row["chi2"])
    best_dh = min(valid, key=lambda row: row["DH_diag_chi2"])
    return {
        "description": "Scan of background-vs-growth projection for the spinor torsion term.",
        "status": "spin-background-projection-scan-computed",
        "base_spin_coeff": base_spin,
        "xi_growth_locked": 1.0,
        "rows": rows,
        "valid_count": len(valid),
        "best_total_chi2": best,
        "best_radial_DH": best_dh,
        "scenario": classify_best_xi(best),
        "passes_bao_shape_gate": best["chi2"] < 30.0,
        "interpretation": (
            "xi_bg controls how much of the spinor a^-6 term is allowed to enter the homogeneous "
            "photon/BAO background. xi_growth remains locked to 1 for the growth sector."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Spin Background Projection",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Base spin coeff: {payload['base_spin_coeff']}",
        f"xi_growth locked: {payload['xi_growth_locked']}",
        f"Scenario: {payload['scenario']}",
        f"Passes BAO shape gate: {payload['passes_bao_shape_gate']}",
        "",
        "## Scan",
        "",
        "| xi_bg | valid | chi2 | chi2/dof | DH chi2 | DH max pull | scale |",
        "|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['xi_bg']:.3g} | {row['valid']} | {row['chi2']:.6g} | "
            f"{row['reduced_chi2']:.6g} | {row['DH_diag_chi2']:.6g} | "
            f"{row['DH_max_abs_pull']:.6g} | {row['scale']:.6g} |"
        )
    best = payload["best_total_chi2"]
    lines.extend(
        [
            "",
            "## Best",
            "",
            f"- best xi_bg: {best['xi_bg']}",
            f"- chi2: {best['chi2']:.6g}",
            f"- chi2/dof: {best['reduced_chi2']:.6g}",
            f"- DH chi2: {best['DH_diag_chi2']:.6g}",
            "",
            "## Interpretation",
            "",
            payload["interpretation"],
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = run_projection_scan()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
