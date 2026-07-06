"""Materialize F_reg components from active Z2/Sigma geometric primitives."""

from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np

from .z2_sigma_global_regularity import (
    FORBIDDEN_PROVENANCE,
    validate_global_regular_component_payload,
)


def _array(payload: dict, key: str) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if not np.all(np.isfinite(values)):
        raise ValueError(f"{key} contains non-finite values")
    return values


def _clean_source(value: object, name: str) -> str:
    text = str(value).strip()
    if not text:
        raise ValueError(f"{name} provenance must be nonempty")
    lowered = text.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE):
        raise ValueError(f"Forbidden {name} provenance: {text}")
    return text


def _frobenius_scaled(matrix: np.ndarray, norm: float) -> float:
    if not math.isfinite(norm) or norm <= 0.0:
        raise ValueError("defect norm must be positive and finite")
    return float(np.sum(np.asarray(matrix, dtype=float) ** 2) / norm)


def normal_holonomy_defect(
    lambda_grid: np.ndarray,
    u_grid: np.ndarray,
    omega: np.ndarray,
    deck_frame_map: np.ndarray | None = None,
) -> np.ndarray:
    if omega.ndim != 4 or omega.shape[0] != lambda_grid.size or omega.shape[1] != u_grid.size:
        raise ValueError("normal_connection_omega_perp_lambda_u must have shape [lambda,u,d,d]")
    if omega.shape[2] != omega.shape[3]:
        raise ValueError("normal connection matrices must be square")
    dim = omega.shape[2]
    if deck_frame_map is None:
        deck_frame_map = np.repeat(np.eye(dim)[None, :, :], lambda_grid.size, axis=0)
    if deck_frame_map.shape != (lambda_grid.size, dim, dim):
        raise ValueError("deck_frame_map_lambda must have shape [lambda,d,d]")
    defects = []
    du = np.diff(u_grid)
    if np.any(du <= 0.0):
        raise ValueError("collar_coordinate_u_grid must be strictly increasing")
    for lam_index in range(lambda_grid.size):
        transport = np.eye(dim)
        for step, width in enumerate(du):
            midpoint_omega = 0.5 * (omega[lam_index, step] + omega[lam_index, step + 1])
            transport = (np.eye(dim) + midpoint_omega * width) @ transport
        closed_transport = deck_frame_map[lam_index] @ transport
        defects.append(_frobenius_scaled(closed_transport - np.eye(dim), float(dim)))
    return np.asarray(defects, dtype=float)


def endpoint_mismatch_defect(h_plus: np.ndarray, h_minus: np.ndarray, tau_pullback: np.ndarray, norms: np.ndarray) -> np.ndarray:
    if h_plus.shape != h_minus.shape or h_plus.ndim != 3 or h_plus.shape[1] != h_plus.shape[2]:
        raise ValueError("endpoint metrics must have shape [lambda,d,d]")
    if tau_pullback.shape != h_plus.shape:
        raise ValueError("tau_Z2_pullback_matrix_on_endpoint_tangents must align with endpoint metrics")
    if norms.shape != (h_plus.shape[0],):
        raise ValueError("endpoint_metric_norm must align with lambda_grid")
    defects = []
    for hp, hm, pullback, norm in zip(h_plus, h_minus, tau_pullback, norms, strict=True):
        pulled = pullback.T @ hm @ pullback
        defects.append(_frobenius_scaled(pulled - hp, float(norm)))
    return np.asarray(defects, dtype=float)


def junction_bianchi_defect(divergence: np.ndarray, flux: np.ndarray, norms: np.ndarray) -> np.ndarray:
    if divergence.shape != flux.shape or divergence.ndim != 2:
        raise ValueError("S divergence and bulk normal flux jump must have shape [lambda,d]")
    if norms.shape != (divergence.shape[0],):
        raise ValueError("surface_vector_norm must align with lambda_grid")
    residual = divergence + flux
    return np.asarray(
        [_frobenius_scaled(vector, float(norm)) for vector, norm in zip(residual, norms, strict=True)],
        dtype=float,
    )


def validate_and_materialize_freg_components(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("F_reg primitive active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_global_regularity_primitives":
        raise ValueError("source must be active_global_regularity_primitives")
    for flag in [
        "compressed_planck_lcdm_used",
        "archived_z4_reuse_used",
        "observational_fit_used",
        "torus_replacement_used",
        "full_no_fit_prediction_ready",
    ]:
        if payload.get(flag) is not False:
            raise ValueError(f"{flag} must be false")

    lambda_grid = _array(payload, "lambda_grid")
    if lambda_grid.ndim != 1 or np.any(lambda_grid <= 0.0) or np.any(np.diff(lambda_grid) <= 0.0):
        raise ValueError("lambda_grid must be positive and strictly increasing")
    u_grid = _array(payload, "collar_coordinate_u_grid")
    if u_grid.ndim != 1 or u_grid.size < 2:
        raise ValueError("collar_coordinate_u_grid must contain at least two points")

    holonomy = normal_holonomy_defect(
        lambda_grid,
        u_grid,
        _array(payload, "normal_connection_omega_perp_lambda_u"),
        _array(payload, "deck_frame_map_lambda")
        if "deck_frame_map_lambda" in payload
        else None,
    )
    endpoint = endpoint_mismatch_defect(
        _array(payload, "h_plus_endpoint_lambda"),
        _array(payload, "h_minus_endpoint_lambda"),
        _array(payload, "tau_Z2_pullback_matrix_on_endpoint_tangents"),
        _array(payload, "endpoint_metric_norm"),
    )
    bianchi = junction_bianchi_defect(
        _array(payload, "S_Sigma_divergence_lambda"),
        _array(payload, "bulk_normal_flux_jump_lambda"),
        _array(payload, "surface_vector_norm"),
    )

    provenance = payload.get("primitive_provenance", {})
    component_payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_global_regularity_components",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "lambda_grid": lambda_grid.tolist(),
        "normal_frame_holonomy_defect": holonomy.tolist(),
        "collar_endpoint_mismatch": endpoint.tolist(),
        "junction_bianchi_defect": bianchi.tolist(),
        "root_tolerance": float(payload.get("root_tolerance", 1.0e-10)),
        "component_provenance": {
            "normal_frame_holonomy_defect": _clean_source(
                provenance.get("normal_connection_omega_perp_lambda_u", ""),
                "normal_connection_omega_perp_lambda_u",
            ),
            "collar_endpoint_mismatch": _clean_source(
                provenance.get("endpoint_collar_metrics_and_z2_pullback", ""),
                "endpoint_collar_metrics_and_z2_pullback",
            ),
            "junction_bianchi_defect": _clean_source(
                provenance.get("sigma_stress_and_bulk_normal_flux", ""),
                "sigma_stress_and_bulk_normal_flux",
            ),
        },
    }
    return validate_global_regular_component_payload(component_payload)


def load_and_materialize_freg_components(path: Path) -> dict:
    return validate_and_materialize_freg_components(
        json.loads(Path(path).read_text(encoding="utf-8"))
    )
