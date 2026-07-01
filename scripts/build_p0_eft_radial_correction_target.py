from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.data import ensure_default_data, load_desi_bao

try:
    from scripts.build_p0_eft_desi_bao_residual_diagnostics import score_shape, split_distance_row
    from scripts.build_p0_eft_desi_dh_inverse_hubble_diagnostic import build_payload as dh_inverse_payload
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_desi_bao_residual_diagnostics import score_shape, split_distance_row
    from build_p0_eft_desi_dh_inverse_hubble_diagnostic import build_payload as dh_inverse_payload
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_radial_correction_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_radial_correction_target.json")


def radial_multiplier(z: float, intercept: float, slope: float) -> float:
    return intercept + slope * z


def corrected_shape(intercept: float, slope: float) -> np.ndarray:
    ensure_default_data()
    dataset = load_desi_bao()
    constants, radion = master_branch_background(z_max=max(float(z) for z in dataset.z))
    constants = {**constants, "spin_coeff": 0.0}
    values = []
    for z, quantity in zip(dataset.z, dataset.quantity):
        zf = float(z)
        row = split_distance_row(zf, constants, radion, z_sigma=float(constants["z_sigma"]))
        radial = radial_multiplier(zf, intercept, slope)
        if quantity == "DM_over_rs":
            values.append(row["D_M_unit"])
        elif quantity == "DH_over_rs":
            values.append(row["D_H_unit"] * radial)
        elif quantity == "DV_over_rs":
            values.append(row["D_V_unit"] * radial ** (1.0 / 3.0))
        else:
            raise ValueError(f"unsupported BAO quantity: {quantity}")
    return np.asarray(values, dtype=float)


def scan_local_grid(center_intercept: float, center_slope: float) -> list[dict]:
    rows = []
    for di in [-0.04, -0.02, 0.0, 0.02, 0.04]:
        for ds in [-0.04, -0.02, 0.0, 0.02, 0.04]:
            intercept = center_intercept + di
            slope = center_slope + ds
            if intercept <= 0:
                continue
            score = score_shape(corrected_shape(intercept, slope))
            rows.append(
                {
                    "intercept": intercept,
                    "slope": slope,
                    "chi2": score["chi2"],
                    "reduced_chi2": score["reduced_chi2"],
                    "scale": score["scale"],
                    "DH_diag_chi2": score["by_quantity"]["DH_over_rs"]["diag_chi2"],
                    "DM_diag_chi2": score["by_quantity"]["DM_over_rs"]["diag_chi2"],
                    "DV_diag_chi2": score["by_quantity"]["DV_over_rs"]["diag_chi2"],
                }
            )
    return rows


def build_payload() -> dict:
    inverse = dh_inverse_payload()
    fit = inverse["linear_multiplier_fit"]
    baseline = score_shape(corrected_shape(1.0, 0.0))
    linear_score = score_shape(corrected_shape(fit["intercept"], fit["slope"]))
    scan_rows = scan_local_grid(fit["intercept"], fit["slope"])
    best = min(scan_rows, key=lambda row: row["chi2"])
    return {
        "description": "Radial correction target for Janus-Holst BAO after spin background screening.",
        "status": "radial-correction-target-scored",
        "linear_target": fit,
        "baseline_no_radial_correction": {
            "chi2": baseline["chi2"],
            "reduced_chi2": baseline["reduced_chi2"],
            "by_quantity": baseline["by_quantity"],
        },
        "linear_target_score": {
            "chi2": linear_score["chi2"],
            "reduced_chi2": linear_score["reduced_chi2"],
            "scale": linear_score["scale"],
            "by_quantity": linear_score["by_quantity"],
        },
        "best_local_grid": best,
        "grid_rows": scan_rows,
        "passes_shape_gate": best["chi2"] < 30.0,
        "is_derived_geometry": False,
        "next_required": "derive the radial multiplier from Janus photon/redshift geometry instead of fitting it.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Radial Correction Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Passes shape gate: {payload['passes_shape_gate']}",
        f"Derived geometry: {payload['is_derived_geometry']}",
        "",
        "## Linear Target From Inverse D_H",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["linear_target"].items())
    lines.extend(
        [
            "",
            "## Scores",
            "",
            f"- baseline chi2: {payload['baseline_no_radial_correction']['chi2']:.6g}",
            f"- linear target chi2: {payload['linear_target_score']['chi2']:.6g}",
            f"- best local grid chi2: {payload['best_local_grid']['chi2']:.6g}",
            f"- best intercept: {payload['best_local_grid']['intercept']:.6g}",
            f"- best slope: {payload['best_local_grid']['slope']:.6g}",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )
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
