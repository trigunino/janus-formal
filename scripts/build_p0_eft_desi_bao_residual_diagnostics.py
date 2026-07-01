from __future__ import annotations

from pathlib import Path
from functools import lru_cache
import json
import math

import numpy as np

from janus_lab.data import ensure_default_data, load_desi_bao
from janus_lab.statistics import chi_square

try:
    from scripts.build_p0_eft_desi_dr2_bao_gate import fit_bao_scale
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import (
        e2_janus_holst,
        master_branch_background,
        trapezoid_integral,
    )
except ModuleNotFoundError:
    from build_p0_eft_desi_dr2_bao_gate import fit_bao_scale
    from build_p0_eft_janus_holst_distance_ruler_map import (
        e2_janus_holst,
        master_branch_background,
        trapezoid_integral,
    )


REPORT_PATH = Path("outputs/reports/p0_eft_desi_bao_residual_diagnostics.md")
JSON_PATH = Path("outputs/reports/p0_eft_desi_bao_residual_diagnostics.json")


def split_distance_row(
    z: float,
    constants: dict,
    radion: list[dict],
    *,
    z_sigma: float,
    radial_jump: float = 1.0,
    transverse_jump: float = 1.0,
    samples: int = 192,
) -> dict:
    if z == 0.0:
        e = math.sqrt(e2_janus_holst(1.0, constants, radion))
        return {"z": z, "E": e, "D_H_unit": 1.0 / e, "D_M_unit": 0.0, "D_V_unit": 0.0}

    def inv_e(value: float) -> float:
        return 1.0 / math.sqrt(e2_janus_holst(1.0 / (1.0 + value), constants, radion))

    e = 1.0 / inv_e(z)
    d_h = inv_e(z) * (radial_jump if z > z_sigma else 1.0)
    if z <= z_sigma:
        zs = [z * i / (samples - 1) for i in range(samples)]
        d_m = trapezoid_integral(zs, [inv_e(value) for value in zs])
    else:
        low = [z_sigma * i / (samples - 1) for i in range(samples)]
        high = [z_sigma + (z - z_sigma) * i / (samples - 1) for i in range(samples)]
        d_m_low = trapezoid_integral(low, [inv_e(value) for value in low])
        d_m_high = trapezoid_integral(high, [inv_e(value) for value in high])
        d_m = d_m_low + transverse_jump * d_m_high
    d_v = (z * d_m * d_m * d_h) ** (1.0 / 3.0)
    return {"z": z, "E": e, "D_H_unit": d_h, "D_M_unit": d_m, "D_V_unit": d_v}


@lru_cache(maxsize=None)
def prediction_shape(radial_jump: float = 1.0, transverse_jump: float = 1.0) -> tuple[float, ...]:
    ensure_default_data()
    dataset = load_desi_bao()
    constants, radion = master_branch_background(z_max=max(float(z) for z in dataset.z))
    z_sigma = float(constants["z_sigma"])
    values = []
    for z, quantity in zip(dataset.z, dataset.quantity):
        row = split_distance_row(
            float(z),
            constants,
            radion,
            z_sigma=z_sigma,
            radial_jump=radial_jump,
            transverse_jump=transverse_jump,
        )
        if quantity == "DM_over_rs":
            values.append(row["D_M_unit"])
        elif quantity == "DH_over_rs":
            values.append(row["D_H_unit"])
        elif quantity == "DV_over_rs":
            values.append(row["D_V_unit"])
        else:
            raise ValueError(f"unsupported BAO quantity: {quantity}")
    return tuple(float(value) for value in values)


def score_shape(shape: np.ndarray) -> dict:
    dataset = load_desi_bao()
    shape = np.asarray(shape, dtype=float)
    scale, chi2 = fit_bao_scale(shape, dataset.value, dataset.covariance)
    prediction = scale * shape
    residual = prediction - dataset.value
    sigma = np.sqrt(np.diag(dataset.covariance))
    rows = []
    for index, (z, quantity, observed, model, error) in enumerate(
        zip(dataset.z, dataset.quantity, dataset.value, prediction, sigma)
    ):
        rows.append(
            {
                "index": int(index),
                "z": float(z),
                "quantity": str(quantity),
                "observed": float(observed),
                "model": float(model),
                "sigma_diag": float(error),
                "residual": float(model - observed),
                "diag_pull": float((model - observed) / error),
            }
        )
    by_quantity = {}
    for quantity in sorted(set(str(q) for q in dataset.quantity)):
        selected = [row for row in rows if row["quantity"] == quantity]
        by_quantity[quantity] = {
            "count": len(selected),
            "max_abs_diag_pull": max(abs(row["diag_pull"]) for row in selected),
            "mean_abs_fractional_residual": float(
                np.mean([abs(row["residual"] / row["observed"]) for row in selected])
            ),
            "diag_chi2": sum(row["diag_pull"] ** 2 for row in selected),
        }
    return {
        "scale": scale,
        "chi2": chi2,
        "dof": int(len(dataset.value) - 1),
        "reduced_chi2": chi2 / (len(dataset.value) - 1),
        "rows": rows,
        "by_quantity": by_quantity,
    }


def scan_junctions() -> dict:
    grid = [0.2, 0.33, 0.5, 0.67, 1.0, 1.5, 2.0, 3.0]
    rows = []
    for radial in grid:
        for transverse in grid:
            score = score_shape(prediction_shape(radial, transverse))
            rows.append(
                {
                    "radial_jump": radial,
                    "transverse_jump": transverse,
                    "scale": score["scale"],
                    "chi2": score["chi2"],
                    "reduced_chi2": score["reduced_chi2"],
                }
            )
    return min(rows, key=lambda row: row["chi2"]) | {"scanned_nodes": len(rows)}


@lru_cache(maxsize=1)
def build_payload() -> dict:
    base_score = score_shape(prediction_shape())
    best_split = scan_junctions()
    best_score = score_shape(prediction_shape(best_split["radial_jump"], best_split["transverse_jump"]))
    return {
        "description": "DESI DR2 BAO residual diagnostics for the Janus-Holst late-distance map.",
        "status": "desi-bao-residual-diagnostics-computed",
        "baseline_no_junction": {
            key: base_score[key] for key in ["scale", "chi2", "dof", "reduced_chi2", "by_quantity"]
        },
        "baseline_residuals": base_score["rows"],
        "best_split_junction_scan": best_split,
        "best_split_by_quantity": best_score["by_quantity"],
        "diagnosis": {
            "radial_DH_problem": base_score["by_quantity"].get("DH_over_rs", {}).get("diag_chi2", 0.0),
            "transverse_DM_problem": base_score["by_quantity"].get("DM_over_rs", {}).get("diag_chi2", 0.0),
            "isotropic_DV_problem": base_score["by_quantity"].get("DV_over_rs", {}).get("diag_chi2", 0.0),
            "split_junction_rescues_shape": best_split["chi2"] < 30.0,
        },
        "verdict": (
            "If the split-junction scan remains high-chi2, the failure is not just a missing "
            "membrane kink in photon distances; the acoustic ruler/redshift map or background "
            "expansion must change."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT DESI BAO Residual Diagnostics",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Baseline",
        "",
        f"- chi2: {payload['baseline_no_junction']['chi2']:.6g}",
        f"- chi2/dof: {payload['baseline_no_junction']['reduced_chi2']:.6g}",
        f"- scale: {payload['baseline_no_junction']['scale']:.6g}",
        "",
        "## By Quantity",
        "",
        "| quantity | count | diag chi2 | max abs diag pull | mean abs fractional residual |",
        "|---|---:|---:|---:|---:|",
    ]
    for quantity, row in payload["baseline_no_junction"]["by_quantity"].items():
        lines.append(
            f"| {quantity} | {row['count']} | {row['diag_chi2']:.6g} | "
            f"{row['max_abs_diag_pull']:.6g} | {row['mean_abs_fractional_residual']:.6g} |"
        )
    best = payload["best_split_junction_scan"]
    lines.extend(
        [
            "",
            "## Best Split-Junction Scan",
            "",
            f"- radial_jump: {best['radial_jump']}",
            f"- transverse_jump: {best['transverse_jump']}",
            f"- chi2: {best['chi2']:.6g}",
            f"- chi2/dof: {best['reduced_chi2']:.6g}",
            f"- scanned nodes: {best['scanned_nodes']}",
            f"- split junction rescues shape: {payload['diagnosis']['split_junction_rescues_shape']}",
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
