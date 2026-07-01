from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.data import ensure_default_data, load_desi_bao

try:
    from scripts.build_p0_eft_desi_bao_residual_diagnostics import score_shape, split_distance_row
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_desi_bao_residual_diagnostics import score_shape, split_distance_row
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_bao_redshift_remap_diagnostic.md")
JSON_PATH = Path("outputs/reports/p0_eft_bao_redshift_remap_diagnostic.json")


def shape_with_remap(radial_power: float = 0.0, transverse_power: float = 0.0) -> np.ndarray:
    ensure_default_data()
    dataset = load_desi_bao()
    constants, radion = master_branch_background(z_max=max(float(z) for z in dataset.z))
    constants = {**constants, "spin_coeff": 0.0}
    values = []
    for z, quantity in zip(dataset.z, dataset.quantity):
        zf = float(z)
        row = split_distance_row(zf, constants, radion, z_sigma=float(constants["z_sigma"]))
        a = 1.0 / (1.0 + zf)
        radial_weight = a**radial_power
        transverse_weight = a**transverse_power
        if quantity == "DM_over_rs":
            values.append(row["D_M_unit"] * transverse_weight)
        elif quantity == "DH_over_rs":
            values.append(row["D_H_unit"] * radial_weight)
        elif quantity == "DV_over_rs":
            values.append(row["D_V_unit"] * (transverse_weight * transverse_weight * radial_weight) ** (1.0 / 3.0))
        else:
            raise ValueError(f"unsupported BAO quantity: {quantity}")
    return np.asarray(values, dtype=float)


def scan_remap() -> dict:
    powers = [-3.0, -2.5, -2.0, -1.5, -1.0, -0.5, 0.0, 0.5, 1.0, 1.5, 2.0]
    rows = []
    for radial in powers:
        for transverse in powers:
            score = score_shape(shape_with_remap(radial, transverse))
            rows.append(
                {
                    "radial_power": radial,
                    "transverse_power": transverse,
                    "chi2": score["chi2"],
                    "reduced_chi2": score["reduced_chi2"],
                    "scale": score["scale"],
                    "DH_diag_chi2": score["by_quantity"]["DH_over_rs"]["diag_chi2"],
                    "DM_diag_chi2": score["by_quantity"]["DM_over_rs"]["diag_chi2"],
                    "DV_diag_chi2": score["by_quantity"]["DV_over_rs"]["diag_chi2"],
                }
            )
    best = min(rows, key=lambda row: row["chi2"])
    radial_only = min([row for row in rows if row["transverse_power"] == 0.0], key=lambda row: row["chi2"])
    transverse_only = min([row for row in rows if row["radial_power"] == 0.0], key=lambda row: row["chi2"])
    return {
        "description": "BAO redshift-dependent remap diagnostic after spin background screening.",
        "status": "bao-redshift-remap-diagnostic-computed",
        "ansatz": "D_H -> D_H*a^p_radial, D_M -> D_M*a^p_transverse, D_V uses the geometric mean.",
        "rows": rows,
        "best": best,
        "best_radial_only": radial_only,
        "best_transverse_only": transverse_only,
        "passes_shape_gate": best["chi2"] < 30.0,
        "interpretation": (
            "A good radial-only solution points to H(z)/redshift mapping. A good transverse-only "
            "solution points to photon distance projection. If only the two-power scan works, the "
            "missing map is anisotropic."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT BAO Redshift Remap Diagnostic",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Ansatz: {payload['ansatz']}",
        f"Passes shape gate: {payload['passes_shape_gate']}",
        "",
        "## Best",
    ]
    for key, value in payload["best"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "## One-Axis Checks", ""])
    lines.append(f"- radial only: {payload['best_radial_only']}")
    lines.append(f"- transverse only: {payload['best_transverse_only']}")
    lines.extend(
        [
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
    payload = scan_remap()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
