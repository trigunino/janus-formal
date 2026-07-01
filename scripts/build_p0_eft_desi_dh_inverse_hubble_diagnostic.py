from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.data import ensure_default_data, load_desi_bao

try:
    from scripts.build_p0_eft_desi_bao_residual_diagnostics import split_distance_row
    from scripts.build_p0_eft_desi_dr2_bao_gate import fit_bao_scale
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_desi_bao_residual_diagnostics import split_distance_row
    from build_p0_eft_desi_dr2_bao_gate import fit_bao_scale
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_desi_dh_inverse_hubble_diagnostic.md")
JSON_PATH = Path("outputs/reports/p0_eft_desi_dh_inverse_hubble_diagnostic.json")


def dh_rows() -> tuple[list[dict], float]:
    ensure_default_data()
    dataset = load_desi_bao()
    constants, radion = master_branch_background(z_max=max(float(z) for z in dataset.z))
    constants = {**constants, "spin_coeff": 0.0}
    shape = []
    for z, quantity in zip(dataset.z, dataset.quantity):
        row = split_distance_row(float(z), constants, radion, z_sigma=float(constants["z_sigma"]))
        if quantity == "DM_over_rs":
            shape.append(row["D_M_unit"])
        elif quantity == "DH_over_rs":
            shape.append(row["D_H_unit"])
        elif quantity == "DV_over_rs":
            shape.append(row["D_V_unit"])
        else:
            raise ValueError(f"unsupported BAO quantity: {quantity}")
    scale, _chi2 = fit_bao_scale(np.asarray(shape), dataset.value, dataset.covariance)

    rows = []
    for z, quantity, observed, model_shape in zip(dataset.z, dataset.quantity, dataset.value, shape):
        if str(quantity) != "DH_over_rs":
            continue
        model_dh = scale * model_shape
        ratio_model_over_observed = model_dh / float(observed)
        rows.append(
            {
                "z": float(z),
                "observed_DH_over_ruler": float(observed),
                "model_DH_over_ruler": float(model_dh),
                "DH_model_over_observed": float(ratio_model_over_observed),
                "E_model_over_E_required": float(1.0 / ratio_model_over_observed),
                "required_DH_multiplier": float(1.0 / ratio_model_over_observed),
            }
        )
    return rows, scale


def fit_linear_ratio(rows: list[dict]) -> dict:
    z = np.asarray([row["z"] for row in rows], dtype=float)
    y = np.asarray([row["required_DH_multiplier"] for row in rows], dtype=float)
    design = np.column_stack([np.ones_like(z), z])
    coeffs, *_ = np.linalg.lstsq(design, y, rcond=None)
    pred = design @ coeffs
    rms = float(np.sqrt(np.mean((pred - y) ** 2)))
    return {"intercept": float(coeffs[0]), "slope": float(coeffs[1]), "rms": rms}


def build_payload() -> dict:
    rows, scale = dh_rows()
    fit = fit_linear_ratio(rows)
    multipliers = [row["required_DH_multiplier"] for row in rows]
    return {
        "description": "Inverse DESI D_H diagnostic for the post-screening Janus-Holst background.",
        "status": "desi-dh-inverse-hubble-diagnostic-computed",
        "bao_scale_from_full_vector": scale,
        "rows": rows,
        "required_multiplier_min": min(multipliers),
        "required_multiplier_max": max(multipliers),
        "required_multiplier_span": max(multipliers) - min(multipliers),
        "linear_multiplier_fit": fit,
        "simple_constant_rescale_sufficient": (max(multipliers) - min(multipliers)) < 0.05,
        "diagnosis": (
            "required_DH_multiplier is the factor by which the Janus radial distance must be "
            "multiplied, equivalently the factor by which E(z)=H/H0 must be reduced, to match "
            "DESI D_H after the global BAO scale is fitted."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT DESI D_H Inverse Hubble Diagnostic",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"BAO scale from full vector: {payload['bao_scale_from_full_vector']:.6g}",
        f"Required multiplier min: {payload['required_multiplier_min']:.6g}",
        f"Required multiplier max: {payload['required_multiplier_max']:.6g}",
        f"Required multiplier span: {payload['required_multiplier_span']:.6g}",
        f"Simple constant rescale sufficient: {payload['simple_constant_rescale_sufficient']}",
        "",
        "## D_H Rows",
        "",
        "| z | observed | model | model/obs | required D_H multiplier | E_model/E_required |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['z']:.3f} | {row['observed_DH_over_ruler']:.6g} | "
            f"{row['model_DH_over_ruler']:.6g} | {row['DH_model_over_observed']:.6g} | "
            f"{row['required_DH_multiplier']:.6g} | {row['E_model_over_E_required']:.6g} |"
        )
    fit = payload["linear_multiplier_fit"]
    lines.extend(
        [
            "",
            "## Linear Multiplier Fit",
            "",
            f"- intercept: {fit['intercept']:.6g}",
            f"- slope: {fit['slope']:.6g}",
            f"- rms: {fit['rms']:.6g}",
            "",
            "## Diagnosis",
            "",
            payload["diagnosis"],
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
