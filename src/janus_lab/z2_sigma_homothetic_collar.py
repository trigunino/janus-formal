"""Homothetic Z2/Sigma collar regularity reductions."""

from __future__ import annotations

import numpy as np

from .z2_sigma_global_regularity import validate_global_regular_component_payload


def _matrix(values, name: str) -> np.ndarray:
    matrix = np.asarray(values, dtype=float)
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError(f"{name} must be a square matrix")
    if not np.all(np.isfinite(matrix)):
        raise ValueError(f"{name} must be finite")
    return matrix


def homothetic_endpoint_defect_values(
    *,
    lambda_grid,
    q_plus,
    q_minus,
    tau_pullback,
) -> np.ndarray:
    """Return normalized endpoint mismatch for h_pm(lambda)=lambda^2 q_pm."""

    lambdas = np.asarray(lambda_grid, dtype=float)
    if lambdas.ndim != 1 or np.any(lambdas <= 0.0) or np.any(np.diff(lambdas) <= 0.0):
        raise ValueError("lambda_grid must be positive and strictly increasing")
    qp = _matrix(q_plus, "q_plus")
    qm = _matrix(q_minus, "q_minus")
    pullback = _matrix(tau_pullback, "tau_pullback")
    if qp.shape != qm.shape or qp.shape != pullback.shape:
        raise ValueError("q_plus, q_minus and tau_pullback must align")
    delta = pullback.T @ qm @ pullback - qp
    norm = float(np.sum(qp * qp))
    if norm <= 0.0:
        raise ValueError("q_plus norm must be positive")
    defect = float(np.sum(delta * delta) / norm)
    return np.full_like(lambdas, defect, dtype=float)


def homothetic_constant_regular_payload(
    *,
    lambda_grid,
    endpoint_defect,
    normal_holonomy_defect=0.0,
    junction_bianchi_defect=0.0,
) -> dict:
    """Build validated F_reg payload for lambda-independent homothetic data."""

    lambdas = np.asarray(lambda_grid, dtype=float)
    endpoint = np.asarray(endpoint_defect, dtype=float)
    if endpoint.shape != lambdas.shape:
        raise ValueError("endpoint_defect must align with lambda_grid")
    holonomy = np.full_like(lambdas, float(normal_holonomy_defect), dtype=float)
    bianchi = np.full_like(lambdas, float(junction_bianchi_defect), dtype=float)
    return validate_global_regular_component_payload(
        {
            "active_core": "Z2_tunnel_Sigma",
            "source": "active_global_regularity_components",
            "compressed_planck_lcdm_used": False,
            "archived_z4_reuse_used": False,
            "observational_fit_used": False,
            "torus_replacement_used": False,
            "full_no_fit_prediction_ready": False,
            "lambda_grid": lambdas.tolist(),
            "normal_frame_holonomy_defect": holonomy.tolist(),
            "collar_endpoint_mismatch": endpoint.tolist(),
            "junction_bianchi_defect": bianchi.tolist(),
            "root_tolerance": 1.0e-12,
            "component_provenance": {
                "normal_frame_holonomy_defect": "active_homothetic_collar_lambda_independent_normal_data",
                "collar_endpoint_mismatch": "active_homothetic_collar_lambda_squared_endpoint_metrics",
                "junction_bianchi_defect": "active_homothetic_collar_lambda_independent_bianchi_data",
            },
        }
    )


def homothetic_collar_radius_selection_status(f_reg_values) -> dict:
    values = np.asarray(f_reg_values, dtype=float)
    if values.ndim != 1 or values.size == 0 or not np.all(np.isfinite(values)):
        raise ValueError("f_reg_values must be finite one-dimensional")
    return {
        "F_reg_lambda_independent": bool(np.allclose(values, values[0])),
        "F_reg_constant_value": float(values[0]),
        "radius_selection_possible": False,
        "reason": (
            "A lambda-independent F_reg is either zero for every sampled lambda "
            "or nonzero for every sampled lambda. It cannot select a unique "
            "R_Sigma/ell_collar."
        ),
    }


def reciprocal_projective_endpoint_defect_values(*, lambda_grid) -> np.ndarray:
    """Endpoint mismatch for a projective reciprocal collar lambda -> 1/lambda.

    In an orthonormal throat frame this compares h_plus=lambda^2 q with
    h_minus=lambda^-2 q using the same tangent frame. The normalized mismatch is
    ((lambda^-2 - lambda^2)^2) / lambda^4 and has its unique positive zero at
    lambda=1 on any sampled grid containing that point.
    """

    lambdas = np.asarray(lambda_grid, dtype=float)
    if lambdas.ndim != 1 or np.any(lambdas <= 0.0) or np.any(np.diff(lambdas) <= 0.0):
        raise ValueError("lambda_grid must be positive and strictly increasing")
    return np.square(np.power(lambdas, -2.0) - np.square(lambdas)) / np.power(lambdas, 4.0)
