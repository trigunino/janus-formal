"""Local tetrad transport formulas for the active Z2/Sigma counterterm."""

from __future__ import annotations

import numpy as np


FORBIDDEN_FLAGS = [
    "compressed_planck_lcdm_background_used",
    "archived_z4_reuse_used",
    "archived_z4_background_reuse_used",
    "phenomenological_holst_bao_scan_used",
    "observational_H0_fit_used",
    "observational_curvature_fit_used",
    "fitted_counterterm_coefficient_used",
]


def _reject_forbidden(payload: dict) -> None:
    for key in FORBIDDEN_FLAGS:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def _unit_q(payload: dict) -> np.ndarray:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("unit q payload active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("unit q payload source must be active_derived")
    _reject_forbidden(payload)
    q = np.asarray(payload.get("unit_intrinsic_metric_q_ab"), dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1]:
        raise ValueError("unit_intrinsic_metric_q_ab must be square")
    if not np.all(np.isfinite(q)) or not np.allclose(q, q.T, atol=1e-12):
        raise ValueError("unit_intrinsic_metric_q_ab must be finite and symmetric")
    if float(np.linalg.det(q)) <= 0.0:
        raise ValueError("unit_intrinsic_metric_q_ab must have positive determinant")
    return q


def _torsion_zero(payload: dict, dim: int) -> bool:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("torsion payload active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("torsion payload source must be active_derived")
    _reject_forbidden(payload)
    torsion = np.asarray(payload.get("torsion_T_internal_I_ab"), dtype=float)
    if torsion.shape != (dim, dim, dim):
        raise ValueError("torsion_T_internal_I_ab shape must match unit q dimension")
    if not np.all(np.isfinite(torsion)):
        raise ValueError("torsion_T_internal_I_ab must be finite")
    return bool(np.allclose(torsion, 0.0, atol=1e-12))


def build_counterterm_tetrad_transport_closure(
    *,
    unit_q_payload: dict,
    torsion_payload: dict,
) -> dict:
    """Derive local collar transport formulas independent of an R(a) solution.

    The active collar ansatz is h_ab(R)=R^2 q_ab. In Gaussian normal gauge,
    K_ab=(1/2) partial_R h_ab=R q_ab.
    """

    q = _unit_q(unit_q_payload)
    dim = int(q.shape[0])
    torsion_zero = _torsion_zero(torsion_payload, dim)
    sqrt_det_q = float(np.sqrt(float(np.linalg.det(q))))

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "route": "symbolic_gaussian_collar_from_unit_q",
        "dimension": dim,
        "sqrt_det_unit_q": sqrt_det_q,
        "tetrad_transport_closed_without_RSigma_values": True,
        "requires_RSigma_values_for_radial_profile": True,
        "metric_transport": {
            "h_ab": "R_Sigma^2 q_ab",
            "delta_e_to_delta_h": "delta h_ab = eta_IJ(delta e_a^I e_b^J + e_a^I delta e_b^J)",
            "partial_R_h_ab": "2 R_Sigma q_ab",
            "trace_h_inv_partial_R_h": f"{2 * dim} / R_Sigma",
            "ready": True,
        },
        "extrinsic_curvature_transport": {
            "gauge": "Gaussian normal collar",
            "K_ab": "1/2 partial_R h_ab = R_Sigma q_ab",
            "partial_R_K_ab": "q_ab",
            "K_trace": f"{dim} / R_Sigma",
            "partial_R_K_trace": f"-{dim} / R_Sigma^2",
            "delta_e_to_delta_K": "delta K_ab = q_ab delta R_Sigma + R_Sigma delta q_ab; active unit-q branch sets delta q_ab=0 for radial counterterm variation",
            "in_allowed_basis": True,
            "ready": True,
        },
        "torsion_pullback_transport": {
            "torsion_pullback_value_zero": torsion_zero,
            "delta_e_T_formula": "delta_e T^I = D_omega(delta e^I)",
            "pullback_formula": "delta_e X_Sigma^*T^I = X_Sigma^*(D_omega delta e^I)",
            "active_pullback_components_used": True,
            "in_allowed_basis": torsion_zero,
            "ready": torsion_zero,
        },
        "counterterm_residual_channel": {
            "tetrad_residual_channel_closed": torsion_zero,
            "residual_one_form_basis": [
                "R_h^{ab} delta h_ab",
                "R_K^{ab} delta K_ab",
                "R_T^A delta T_A",
                "R_chi delta chi",
                "R_Z2 delta epsilon_Z2",
            ],
            "still_requires_residual_coefficients": [
                "R_h^{ab}",
                "R_K^{ab}",
                "R_T^A",
                "R_chi",
            ],
        },
    }
