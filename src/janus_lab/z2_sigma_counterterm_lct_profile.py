"""L_ct radial profile from active Z2/Sigma residual contractions."""

from __future__ import annotations

import numpy as np


FORBIDDEN_PROVENANCE_FLAGS = (
    "compressed_planck_lcdm_background_used",
    "archived_z4_reuse_used",
    "archived_z4_background_reuse_used",
    "phenomenological_holst_bao_scan_used",
    "observational_H0_fit_used",
    "observational_curvature_fit_used",
    "fitted_counterterm_coefficient_used",
)


def reject_forbidden_provenance(payload: dict) -> None:
    for key in FORBIDDEN_PROVENANCE_FLAGS:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def checked_series(payload: dict, key: str, shape: tuple[int, ...]) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if values.shape != shape or not np.all(np.isfinite(values)):
        raise ValueError(f"{key} must be finite and aligned with a_grid")
    return values


def trapezoid_profile_from_radial_derivative(
    *,
    radius: np.ndarray,
    derivative: np.ndarray,
    reference_index: int,
    reference_value: float,
) -> np.ndarray:
    if not 0 <= reference_index < radius.size:
        raise ValueError("reference_index must select an element of the grid")
    profile = np.empty_like(radius)
    profile[reference_index] = reference_value
    for idx in range(reference_index + 1, radius.size):
        d_radius = radius[idx] - radius[idx - 1]
        profile[idx] = profile[idx - 1] + 0.5 * (
            derivative[idx - 1] + derivative[idx]
        ) * d_radius
    for idx in range(reference_index - 1, -1, -1):
        d_radius = radius[idx + 1] - radius[idx]
        profile[idx] = profile[idx + 1] - 0.5 * (
            derivative[idx] + derivative[idx + 1]
        ) * d_radius
    return profile


def build_lct_profile_from_residual_contractions(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("contraction payload active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("contraction payload source must be active_derived")
    reject_forbidden_provenance(payload)
    if payload.get("residual_scalar_contractions_ready") is not True:
        raise ValueError("residual_scalar_contractions_ready must be true")
    if payload.get("L_ct_integration_constant_fixed") is not True:
        raise ValueError("L_ct_integration_constant_fixed must be true")

    a_grid = np.asarray(payload["a_grid"], dtype=float)
    if a_grid.ndim != 1 or a_grid.size < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(a_grid <= 0.0) or np.any(np.diff(a_grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    shape = a_grid.shape
    radius = checked_series(payload, "R_Sigma_values", shape)
    if np.any(radius <= 0.0):
        raise ValueError("R_Sigma_values must be positive")
    rh_q = checked_series(payload, "R_h_q_contract_values", shape)
    rk_q = checked_series(payload, "R_K_q_contract_values", shape)
    rchi_dchi = checked_series(payload, "R_chi_partial_R_chi_values", shape)

    partial_lct = -(2.0 * radius * rh_q + rk_q + rchi_dchi)
    reference_index = int(payload.get("L_ct_reference_index", 0))
    reference_value = float(payload["L_ct_reference_value"])
    if not np.isfinite(reference_value):
        raise ValueError("L_ct_reference_value must be finite")
    lct = trapezoid_profile_from_radial_derivative(
        radius=radius,
        derivative=partial_lct,
        reference_index=reference_index,
        reference_value=reference_value,
    )
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
        "L_ct_profile_ready": True,
        "L_ct_profile_derivation": "integrated active residual scalar contractions",
        "radial_derivative_formula": (
            "partial_R L_ct = -(2 R_Sigma R_h^{ab} q_ab + "
            "R_K^{ab} q_ab + R_chi partial_R chi)"
        ),
        "a_grid": a_grid.tolist(),
        "R_Sigma_values": radius.tolist(),
        "R_h_q_contract_values": rh_q.tolist(),
        "R_K_q_contract_values": rk_q.tolist(),
        "R_chi_partial_R_chi_values": rchi_dchi.tolist(),
        "partial_R_L_ct_values": partial_lct.tolist(),
        "L_ct_values": lct.tolist(),
        "L_ct_reference_index": reference_index,
        "L_ct_reference_value": reference_value,
        "L_ct_integration_constant_fixed": True,
        "contraction_source": payload.get(
            "contraction_source", "counterterm_residual_scalar_contractions_inputs"
        ),
    }
