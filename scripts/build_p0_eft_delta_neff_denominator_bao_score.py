from __future__ import annotations

from pathlib import Path
import json
import math

try:
    from scripts.build_p0_eft_desi_bao_residual_diagnostics import score_shape
    from scripts.build_p0_eft_dv_ruler_residual_target import shape_with_radial_and_dv
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
    from scripts.build_p0_eft_radial_correction_target import build_payload as radial_payload
    from scripts.build_p0_eft_sound_horizon_drag_target import build_payload as sound_target
except ModuleNotFoundError:
    from build_p0_eft_desi_bao_residual_diagnostics import score_shape
    from build_p0_eft_dv_ruler_residual_target import shape_with_radial_and_dv
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
    from build_p0_eft_radial_correction_target import build_payload as radial_payload
    from build_p0_eft_sound_horizon_drag_target import build_payload as sound_target


REPORT_PATH = Path("outputs/reports/p0_eft_delta_neff_denominator_bao_score.md")
JSON_PATH = Path("outputs/reports/p0_eft_delta_neff_denominator_bao_score.json")


def dv_factor_from_delta_neff(delta_neff: float) -> float:
    standard_neff = 3.046
    neutrino_factor = 0.2271
    fractional_e2 = delta_neff * neutrino_factor / (1.0 + neutrino_factor * standard_neff)
    return math.sqrt(1.0 + fractional_e2)


def build_payload() -> dict:
    constants, _ = master_branch_background()
    radial = radial_payload()["best_local_grid"]
    exact = sound_target()["input_dv_factor"]
    base = abs(float(constants["eta_holst"])) * float(constants["Omega_m0"])
    a_sigma = float(constants["a_sigma"])
    cases = [
        {"name": "exact_required", "dv_factor": exact, "derived": False},
        {"name": "denominator_50_empirical", "delta_neff": base * (1.0 + (1.0 - a_sigma) / 50.0), "derived": False},
        {"name": "denominator_48_pin_orbifold_boundary", "delta_neff": base * (1.0 + (1.0 - a_sigma) / 48.0), "derived": False},
        {"name": "base_eta_omega_m", "delta_neff": base, "derived": False},
    ]
    rows = []
    for case in cases:
        if "dv_factor" in case:
            dv_factor = float(case["dv_factor"])
        else:
            dv_factor = dv_factor_from_delta_neff(float(case["delta_neff"]))
        score = score_shape(shape_with_radial_and_dv(radial["intercept"], radial["slope"], dv_factor))
        rows.append(
            {
                **case,
                "dv_factor": dv_factor,
                "chi2": score["chi2"],
                "reduced_chi2": score["reduced_chi2"],
                "DV_diag_chi2": score["by_quantity"]["DV_over_rs"]["diag_chi2"],
                "DH_diag_chi2": score["by_quantity"]["DH_over_rs"]["diag_chi2"],
                "DM_diag_chi2": score["by_quantity"]["DM_over_rs"]["diag_chi2"],
            }
        )
    best = min(rows, key=lambda row: row["chi2"])
    return {
        "description": "DESI BAO score for Delta N_eff residual denominator candidates.",
        "status": "delta-neff-denominator-bao-score-computed",
        "base_delta_neff_eta_omega_m": base,
        "a_sigma": a_sigma,
        "rows": rows,
        "best": best,
        "denominator_48_passes_shape_gate": next(row for row in rows if row["name"].startswith("denominator_48"))["chi2"] < 30.0,
        "is_derived_geometry": False,
        "next_required": "if denominator 48 is acceptable, derive its trace normalization; otherwise keep the residual factor open.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Delta Neff Denominator BAO Score",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Derived geometry: {payload['is_derived_geometry']}",
        f"Denominator 48 passes shape gate: {payload['denominator_48_passes_shape_gate']}",
        "",
        "| case | D_V factor | chi2 | chi2/dof | DV chi2 |",
        "|---|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['name']} | {row['dv_factor']:.6g} | {row['chi2']:.6g} | "
            f"{row['reduced_chi2']:.6g} | {row['DV_diag_chi2']:.6g} |"
        )
    lines.extend(["", "## Next", "", payload["next_required"], ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
