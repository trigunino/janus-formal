"""Normal-frame connection primitives for the Janus Z2/Sigma collar."""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from .z2_sigma_global_regularity import FORBIDDEN_PROVENANCE


REQUIRED_FALSE_FLAGS = [
    "compressed_planck_lcdm_used",
    "archived_z4_reuse_used",
    "observational_fit_used",
    "torus_replacement_used",
    "full_no_fit_prediction_ready",
]


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


def normal_connection_from_frame(
    normal_frame_basis: np.ndarray,
    partial_u_normal_frame_basis: np.ndarray,
    connection_u_matrix: np.ndarray,
    ambient_metric: np.ndarray,
) -> np.ndarray:
    """Compute omega_AB = N_A^mu g_mn (d_u N_B^nu + Gamma_u^nu_r N_B^r)."""
    if normal_frame_basis.ndim != 4:
        raise ValueError("normal_frame_basis_lambda_u must have shape [lambda,u,d_normal,d_ambient]")
    if partial_u_normal_frame_basis.shape != normal_frame_basis.shape:
        raise ValueError("partial_u_normal_frame_basis_lambda_u must match normal_frame_basis_lambda_u")
    n_lambda, n_u, d_normal, d_ambient = normal_frame_basis.shape
    if connection_u_matrix.shape != (n_lambda, n_u, d_ambient, d_ambient):
        raise ValueError("connection_u_matrix_lambda_u must have shape [lambda,u,d_ambient,d_ambient]")
    if ambient_metric.shape != (n_lambda, n_u, d_ambient, d_ambient):
        raise ValueError("ambient_metric_lambda_u must have shape [lambda,u,d_ambient,d_ambient]")

    omega = np.zeros((n_lambda, n_u, d_normal, d_normal), dtype=float)
    for i in range(n_lambda):
        for j in range(n_u):
            basis = normal_frame_basis[i, j]
            cov_derivative = partial_u_normal_frame_basis[i, j] + (
                connection_u_matrix[i, j] @ basis.T
            ).T
            omega[i, j] = basis @ ambient_metric[i, j] @ cov_derivative.T
    return omega


def validate_and_materialize_normal_connection(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_normal_frame_connection_primitives":
        raise ValueError("source must be active_normal_frame_connection_primitives")
    for flag in REQUIRED_FALSE_FLAGS:
        if payload.get(flag) is not False:
            raise ValueError(f"{flag} must be false")

    lambda_grid = _array(payload, "lambda_grid")
    if lambda_grid.ndim != 1 or np.any(lambda_grid <= 0.0) or np.any(np.diff(lambda_grid) <= 0.0):
        raise ValueError("lambda_grid must be positive and strictly increasing")
    u_grid = _array(payload, "collar_coordinate_u_grid")
    if u_grid.ndim != 1 or u_grid.size < 2 or np.any(np.diff(u_grid) <= 0.0):
        raise ValueError("collar_coordinate_u_grid must be strictly increasing")

    omega = normal_connection_from_frame(
        _array(payload, "normal_frame_basis_lambda_u"),
        _array(payload, "partial_u_normal_frame_basis_lambda_u"),
        _array(payload, "connection_u_matrix_lambda_u"),
        _array(payload, "ambient_metric_lambda_u"),
    )
    if omega.shape[:2] != (lambda_grid.size, u_grid.size):
        raise ValueError("normal frame arrays must align with lambda/u grids")

    provenance = payload.get("primitive_provenance", {})
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_normal_connection_from_frame",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "lambda_grid": lambda_grid.tolist(),
        "collar_coordinate_u_grid": u_grid.tolist(),
        "normal_connection_omega_perp_lambda_u": omega.tolist(),
        "normal_connection_ready": True,
        "omega_perp_from_active_normal_frame": True,
        "provenance": {
            "normal_frame_basis_lambda_u": _clean_source(
                provenance.get("normal_frame_basis_lambda_u", ""),
                "normal_frame_basis_lambda_u",
            ),
            "partial_u_normal_frame_basis_lambda_u": _clean_source(
                provenance.get("partial_u_normal_frame_basis_lambda_u", ""),
                "partial_u_normal_frame_basis_lambda_u",
            ),
            "connection_u_matrix_lambda_u": _clean_source(
                provenance.get("connection_u_matrix_lambda_u", ""),
                "connection_u_matrix_lambda_u",
            ),
            "ambient_metric_lambda_u": _clean_source(
                provenance.get("ambient_metric_lambda_u", ""),
                "ambient_metric_lambda_u",
            ),
        },
    }


def load_and_materialize_normal_connection(path: Path) -> dict:
    return validate_and_materialize_normal_connection(
        json.loads(Path(path).read_text(encoding="utf-8"))
    )
