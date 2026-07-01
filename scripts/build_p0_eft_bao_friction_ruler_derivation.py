from __future__ import annotations

from pathlib import Path
import json
import math

try:
    from scripts.build_p0_eft_desi_bao_residual_diagnostics import score_shape
    from scripts.build_p0_eft_dv_ruler_residual_target import shape_with_radial_and_dv
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
    from scripts.build_p0_eft_radial_correction_target import build_payload as radial_payload
except ModuleNotFoundError:
    from build_p0_eft_desi_bao_residual_diagnostics import score_shape
    from build_p0_eft_dv_ruler_residual_target import shape_with_radial_and_dv
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
    from build_p0_eft_radial_correction_target import build_payload as radial_payload


REPORT_PATH = Path("outputs/reports/p0_eft_bao_friction_ruler_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_bao_friction_ruler_derivation.json")


def fine_scan() -> dict:
    radial = radial_payload()["best_local_grid"]
    constants, _ = master_branch_background()
    z_sigma = float(constants["z_sigma"])
    rows = []
    for i in range(81):
        dv_factor = 0.98 + 0.002 * i
        score = score_shape(shape_with_radial_and_dv(radial["intercept"], radial["slope"], dv_factor))
        rows.append(
            {
                "dv_factor": dv_factor,
                "chi2": score["chi2"],
                "reduced_chi2": score["reduced_chi2"],
                "scale": score["scale"],
                "DH_diag_chi2": score["by_quantity"]["DH_over_rs"]["diag_chi2"],
                "DM_diag_chi2": score["by_quantity"]["DM_over_rs"]["diag_chi2"],
                "DV_diag_chi2": score["by_quantity"]["DV_over_rs"]["diag_chi2"],
            }
        )
    best = min(rows, key=lambda row: row["chi2"])
    optical_depth = math.log(best["dv_factor"])
    return {
        "description": "BAO D_V residual recast as a weak Janus-Holst photon/ruler friction target.",
        "status": "bao-friction-ruler-target-scored",
        "radial_input": {"intercept": radial["intercept"], "slope": radial["slope"]},
        "z_sigma": z_sigma,
        "best": best,
        "rows": rows,
        "effective_optical_depth": optical_depth,
        "effective_friction_per_redshift": optical_depth / z_sigma,
        "effective_sound_horizon_ratio": 1.0 / best["dv_factor"],
        "effective_sound_horizon_shrink": 1.0 - 1.0 / best["dv_factor"],
        "passes_shape_gate": best["chi2"] < 30.0,
        "is_derived_geometry": False,
        "next_required": "derive tau_drag = log(D_V_factor) from the Janus-Holst photon transport or drag-epoch ruler equation.",
    }


def render_markdown(payload: dict) -> str:
    best = payload["best"]
    lines = [
        "# P0 EFT BAO Friction Ruler Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Passes shape gate: {payload['passes_shape_gate']}",
        f"Derived geometry: {payload['is_derived_geometry']}",
        "",
        "## Best Fine-Scan Target",
        "",
        f"- D_V factor: {best['dv_factor']:.6g}",
        f"- chi2: {best['chi2']:.6g}",
        f"- chi2/dof: {best['reduced_chi2']:.6g}",
        f"- D_V diag chi2: {best['DV_diag_chi2']:.6g}",
        "",
        "## Friction/Ruler Interpretation",
        "",
        f"- tau_drag = log(D_V factor): {payload['effective_optical_depth']:.6g}",
        f"- tau_drag / z_sigma: {payload['effective_friction_per_redshift']:.6g}",
        f"- r_d Janus / r_d reference: {payload['effective_sound_horizon_ratio']:.6g}",
        f"- inferred ruler shrink: {payload['effective_sound_horizon_shrink']:.6g}",
        "",
        "## Next",
        "",
        payload["next_required"],
        "",
    ]
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = fine_scan()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
