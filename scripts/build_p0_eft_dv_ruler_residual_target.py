from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.data import ensure_default_data, load_desi_bao

try:
    from scripts.build_p0_eft_desi_bao_residual_diagnostics import score_shape, split_distance_row
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
    from scripts.build_p0_eft_radial_correction_target import build_payload as radial_payload
except ModuleNotFoundError:
    from build_p0_eft_desi_bao_residual_diagnostics import score_shape, split_distance_row
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
    from build_p0_eft_radial_correction_target import build_payload as radial_payload


REPORT_PATH = Path("outputs/reports/p0_eft_dv_ruler_residual_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_dv_ruler_residual_target.json")


def shape_with_radial_and_dv(radial_intercept: float, radial_slope: float, dv_factor: float) -> np.ndarray:
    ensure_default_data()
    dataset = load_desi_bao()
    constants, radion = master_branch_background(z_max=max(float(z) for z in dataset.z))
    constants = {**constants, "spin_coeff": 0.0}
    values = []
    for z, quantity in zip(dataset.z, dataset.quantity):
        zf = float(z)
        row = split_distance_row(zf, constants, radion, z_sigma=float(constants["z_sigma"]))
        radial = radial_intercept + radial_slope * zf
        if quantity == "DM_over_rs":
            values.append(row["D_M_unit"])
        elif quantity == "DH_over_rs":
            values.append(row["D_H_unit"] * radial)
        elif quantity == "DV_over_rs":
            values.append(row["D_V_unit"] * radial ** (1.0 / 3.0) * dv_factor)
        else:
            raise ValueError(f"unsupported BAO quantity: {quantity}")
    return np.asarray(values, dtype=float)


def run_scan() -> dict:
    radial = radial_payload()["best_local_grid"]
    rows = []
    for dv_factor in [0.80, 0.85, 0.90, 0.95, 1.0, 1.05, 1.10, 1.15, 1.20]:
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
    return {
        "description": "D_V/ruler residual target after spin screening and radial correction.",
        "status": "dv-ruler-residual-target-scored",
        "radial_input": {"intercept": radial["intercept"], "slope": radial["slope"]},
        "rows": rows,
        "best": best,
        "passes_shape_gate": best["chi2"] < 30.0,
        "is_derived_geometry": False,
        "next_required": "derive the D_V/ruler factor from drag-epoch or isotropic BAO ruler geometry.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT D_V Ruler Residual Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Passes shape gate: {payload['passes_shape_gate']}",
        f"Derived geometry: {payload['is_derived_geometry']}",
        "",
        "## Radial Input",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["radial_input"].items())
    lines.extend(
        [
            "",
            "## D_V Factor Scan",
            "",
            "| D_V factor | chi2 | chi2/dof | DH chi2 | DM chi2 | DV chi2 | scale |",
            "|---:|---:|---:|---:|---:|---:|---:|",
        ]
    )
    for row in payload["rows"]:
        lines.append(
            f"| {row['dv_factor']:.6g} | {row['chi2']:.6g} | {row['reduced_chi2']:.6g} | "
            f"{row['DH_diag_chi2']:.6g} | {row['DM_diag_chi2']:.6g} | "
            f"{row['DV_diag_chi2']:.6g} | {row['scale']:.6g} |"
        )
    best = payload["best"]
    lines.extend(
        [
            "",
            "## Best",
            "",
            f"- D_V factor: {best['dv_factor']}",
            f"- chi2: {best['chi2']:.6g}",
            f"- chi2/dof: {best['reduced_chi2']:.6g}",
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
