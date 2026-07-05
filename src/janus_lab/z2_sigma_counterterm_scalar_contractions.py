"""Scalar contractions for the active Z2/Sigma counterterm residual."""

from __future__ import annotations

import numpy as np

from janus_lab.z2_sigma_counterterm_lct_profile import reject_forbidden_provenance


def _series(payload: dict, key: str, shape: tuple[int, ...]) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if values.shape != shape or not np.all(np.isfinite(values)):
        raise ValueError(f"{key} must be finite and aligned with a_grid")
    return values


def _radius_series(payload: dict, shape: tuple[int, ...]) -> np.ndarray:
    if "R_Sigma_values" in payload:
        key = "R_Sigma_values"
    elif "R_Sigma_of_a" in payload:
        key = "R_Sigma_of_a"
    else:
        raise ValueError("radius payload must provide R_Sigma_values or R_Sigma_of_a")
    values = _series(payload, key, shape)
    if np.any(values <= 0.0):
        raise ValueError(f"{key} must be positive")
    return values


def _tensor_series(payload: dict, key: str, shape: tuple[int, int]) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if values.ndim == 2:
        values = np.broadcast_to(values, (1,) + values.shape)
    if values.ndim != 3 or values.shape[1:] != shape or not np.all(np.isfinite(values)):
        raise ValueError(f"{key} must be finite with shape (n,{shape[0]},{shape[1]}) or {shape}")
    return values


def _active(payload: dict, name: str) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{name} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{name} source must be active_derived")
    reject_forbidden_provenance(payload)


def build_residual_scalar_contractions(
    *,
    q_payload: dict,
    radius_payload: dict,
    metric_payload: dict,
    extrinsic_payload: dict,
    immirzi_payload: dict,
) -> dict:
    for name, payload in {
        "q_payload": q_payload,
        "radius_payload": radius_payload,
        "metric_payload": metric_payload,
        "extrinsic_payload": extrinsic_payload,
        "immirzi_payload": immirzi_payload,
    }.items():
        _active(payload, name)

    q = np.asarray(q_payload["unit_intrinsic_metric_q_ab"], dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1] or not np.all(np.isfinite(q)):
        raise ValueError("unit_intrinsic_metric_q_ab must be a finite square tensor")
    dim = q.shape[0]
    a_grid = np.asarray(radius_payload["a_grid"], dtype=float)
    if a_grid.ndim != 1 or a_grid.size < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(a_grid <= 0.0) or np.any(np.diff(a_grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    shape = a_grid.shape
    radius = _radius_series(radius_payload, shape)

    r_h = _tensor_series(metric_payload, "R_h_ab", (dim, dim))
    r_k = _tensor_series(extrinsic_payload, "R_K_ab", (dim, dim))
    if r_h.shape[0] == 1:
        r_h = np.broadcast_to(r_h, (a_grid.size, dim, dim))
    if r_k.shape[0] == 1:
        r_k = np.broadcast_to(r_k, (a_grid.size, dim, dim))
    if r_h.shape[0] != a_grid.size or r_k.shape[0] != a_grid.size:
        raise ValueError("R_h_ab and R_K_ab series must align with a_grid")

    if "R_chi_partial_R_chi_values" in immirzi_payload:
        rchi_dchi = _series(immirzi_payload, "R_chi_partial_R_chi_values", shape)
    else:
        r_chi = _series(immirzi_payload, "R_chi_values", shape)
        partial_chi = _series(immirzi_payload, "partial_R_chi_values", shape)
        rchi_dchi = r_chi * partial_chi

    rh_q = np.einsum("nab,ab->n", r_h, q)
    rk_q = np.einsum("nab,ab->n", r_k, q)
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
        "residual_scalar_contractions_ready": True,
        "dimension": dim,
        "a_grid": a_grid.tolist(),
        "R_Sigma_values": radius.tolist(),
        "R_h_q_contract_values": rh_q.tolist(),
        "R_K_q_contract_values": rk_q.tolist(),
        "R_chi_partial_R_chi_values": rchi_dchi.tolist(),
        "contraction_formula": {
            "R_h_q": "R_h^{ab} q_ab",
            "R_K_q": "R_K^{ab} q_ab",
            "R_chi_partial_R_chi": "R_chi partial_R chi",
        },
        "contraction_source": "active residual tensors and active q_ab",
        "L_ct_integration_constant_fixed": bool(
            immirzi_payload.get("L_ct_integration_constant_fixed", False)
        ),
        "L_ct_reference_index": int(immirzi_payload.get("L_ct_reference_index", 0)),
        "L_ct_reference_value": float(immirzi_payload.get("L_ct_reference_value", 0.0)),
    }
