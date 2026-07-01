from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab import JanusExpansion, e_lcdm
from janus_lab.bao import bao_prediction_vector, janus_bao_prediction_vector
from janus_lab.data import ensure_default_data, load_desi_bao
from janus_lab.statistics import chi_square

try:
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import distance_row, master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_janus_holst_distance_ruler_map import distance_row, master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_desi_dr2_bao_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_desi_dr2_bao_gate.json")


def fit_bao_scale(shape: np.ndarray, observed: np.ndarray, covariance: np.ndarray) -> tuple[float, float]:
    inv_shape = np.linalg.solve(covariance, shape)
    inv_observed = np.linalg.solve(covariance, observed)
    scale = float(shape @ inv_observed / (shape @ inv_shape))
    chi2 = chi_square(observed - scale * shape, covariance=covariance)
    return scale, chi2


def score_lcdm(omega_m: float) -> dict:
    dataset = load_desi_bao()
    shape = bao_prediction_vector(dataset, lambda z: e_lcdm(z, omega_m=omega_m), scale=1.0, samples=1024)
    scale, chi2 = fit_bao_scale(shape, dataset.value, dataset.covariance)
    return {
        "model": f"Lambda-CDM Om={omega_m}",
        "omega_m": omega_m,
        "scale": scale,
        "chi2": chi2,
        "dof": int(len(dataset.value) - 1),
        "reduced_chi2": chi2 / (len(dataset.value) - 1),
    }


def score_janus_proxy(q0: float) -> dict:
    dataset = load_desi_bao()
    model = JanusExpansion.from_q0(q0)
    shape = janus_bao_prediction_vector(dataset, model, scale=1.0)
    scale, chi2 = fit_bao_scale(shape, dataset.value, dataset.covariance)
    return {
        "model": f"Janus-open-proxy q0={q0}",
        "q0": q0,
        "scale": scale,
        "chi2": chi2,
        "dof": int(len(dataset.value) - 1),
        "reduced_chi2": chi2 / (len(dataset.value) - 1),
    }


def score_holst_distance_shape() -> dict:
    dataset = load_desi_bao()
    constants, radion = master_branch_background(z_max=max(float(z) for z in dataset.z))
    shape = []
    for z, quantity in zip(dataset.z, dataset.quantity):
        row = distance_row(float(z), constants, radion)
        if quantity == "DM_over_rs":
            shape.append(row["D_M_unit"])
        elif quantity == "DH_over_rs":
            shape.append(row["D_H_unit"])
        elif quantity == "DV_over_rs":
            shape.append(row["D_V_unit"])
        else:
            raise ValueError(f"unsupported DESI BAO quantity: {quantity}")
    scale, chi2 = fit_bao_scale(np.asarray(shape, dtype=float), dataset.value, dataset.covariance)
    return {
        "model": "Janus-Holst late-distance shape diagnostic",
        "scale": scale,
        "chi2": chi2,
        "dof": int(len(dataset.value) - 1),
        "reduced_chi2": chi2 / (len(dataset.value) - 1),
        "is_no_fit_bao_likelihood": False,
    }


def build_payload() -> dict:
    ensure_default_data()
    dataset = load_desi_bao()
    covariance_is_symmetric = bool(np.allclose(dataset.covariance, dataset.covariance.T))
    covariance_is_positive = True
    try:
        np.linalg.cholesky(dataset.covariance)
    except np.linalg.LinAlgError:
        covariance_is_positive = False
    lcdm_scores = [score_lcdm(omega_m) for omega_m in [0.30, 0.315, 0.35]]
    janus_scores = [score_janus_proxy(q0) for q0 in [-0.03, -0.05, -0.087]]
    holst_shape = score_holst_distance_shape()
    return {
        "description": "DESI DR2 BAO gate using the published Gaussian BAO vector and covariance.",
        "status": "desi-dr2-bao-loaded-holst-distance-map-open",
        "data_points": int(len(dataset.value)),
        "quantities": sorted(set(str(q) for q in dataset.quantity)),
        "covariance_is_symmetric": covariance_is_symmetric,
        "covariance_is_positive_definite": covariance_is_positive,
        "best_lcdm_control": min(lcdm_scores, key=lambda row: row["chi2"]),
        "lcdm_control_scores": lcdm_scores,
        "janus_open_proxy_scores": janus_scores,
        "holst_bao_shape_diagnostic": holst_shape,
        "holst_bao_shape_diagnostic_scored": True,
        "holst_bao_shape_diagnostic_passes": holst_shape["chi2"] < 30.0,
        "holst_growth_branch_bao_scored": False,
        "janus_holst_late_distance_map_ready": True,
        "janus_holst_distance_ruler_map_ready": False,
        "holst_bao_blocker": (
            "The Holst/membrane branch currently predicts f_sigma8 and growth. "
            "The unified Janus/Holst distance-ruler map with H(z), D_M(z), D_H(z), D_V(z), and r_star/r_d is still required "
            "before a non-ad-hoc DESI BAO likelihood can be assigned to that branch."
        ),
        "next_required": "derive P0EFTJanusHolstDistanceRulerMap, then reuse this DESI DR2 covariance.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT DESI DR2 BAO Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Data points: {payload['data_points']}",
        f"Quantities: {', '.join(payload['quantities'])}",
        f"Covariance symmetric: {payload['covariance_is_symmetric']}",
        f"Covariance positive definite: {payload['covariance_is_positive_definite']}",
        "",
        "## LCDM Control",
        "",
        "| model | scale | chi2 | dof | chi2/dof |",
        "|---|---:|---:|---:|---:|",
    ]
    for row in payload["lcdm_control_scores"]:
        lines.append(
            f"| {row['model']} | {row['scale']:.6g} | {row['chi2']:.6g} | "
            f"{row['dof']} | {row['reduced_chi2']:.6g} |"
        )
    lines.extend(["", "## Janus Open Proxy Guardrail", "", "| model | scale | chi2 | dof | chi2/dof |", "|---|---:|---:|---:|---:|"])
    for row in payload["janus_open_proxy_scores"]:
        lines.append(
            f"| {row['model']} | {row['scale']:.6g} | {row['chi2']:.6g} | "
            f"{row['dof']} | {row['reduced_chi2']:.6g} |"
        )
    lines.extend(
        [
            "",
            "## Janus-Holst Late Distance Shape Diagnostic",
            "",
            "| model | scale | chi2 | dof | chi2/dof | no-fit BAO likelihood |",
            "|---|---:|---:|---:|---:|---:|",
            (
                f"| {payload['holst_bao_shape_diagnostic']['model']} | "
                f"{payload['holst_bao_shape_diagnostic']['scale']:.6g} | "
                f"{payload['holst_bao_shape_diagnostic']['chi2']:.6g} | "
                f"{payload['holst_bao_shape_diagnostic']['dof']} | "
                f"{payload['holst_bao_shape_diagnostic']['reduced_chi2']:.6g} | "
                f"{payload['holst_bao_shape_diagnostic']['is_no_fit_bao_likelihood']} |"
            ),
            "",
            "## Holst Branch Status",
            "",
            f"- Holst BAO shape diagnostic scored: {payload['holst_bao_shape_diagnostic_scored']}",
            f"- Holst BAO shape diagnostic passes: {payload['holst_bao_shape_diagnostic_passes']}",
            f"- Holst growth branch BAO scored: {payload['holst_growth_branch_bao_scored']}",
            f"- Janus/Holst late distance map ready: {payload['janus_holst_late_distance_map_ready']}",
            f"- Janus/Holst distance-ruler map ready: {payload['janus_holst_distance_ruler_map_ready']}",
            f"- Blocker: {payload['holst_bao_blocker']}",
            f"- Next: {payload['next_required']}",
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
