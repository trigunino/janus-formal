"""Variation of an explicit active Z2/Sigma counterterm density."""

from __future__ import annotations

import numpy as np
import sympy as sp

from janus_lab.z2_sigma_counterterm_lct_profile import reject_forbidden_provenance


def _active(payload: dict, name: str) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{name} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{name} source must be active_derived")
    reject_forbidden_provenance(payload)


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
        raise ValueError("density payload must provide R_Sigma_values or R_Sigma_of_a")
    radius = _series(payload, key, shape)
    if np.any(radius <= 0.0):
        raise ValueError(f"{key} must be positive")
    return radius


def _compile_density(payload: dict) -> tuple[sp.Expr, sp.Symbol, sp.Symbol, sp.Symbol]:
    if payload.get("local_density_action_derived") is not True:
        raise ValueError("local_density_action_derived must be true")
    if payload.get("density_expression_status") != "explicit":
        raise ValueError("density_expression_status must be explicit")
    expression = payload.get("L_ct_expression")
    if not isinstance(expression, str) or not expression.strip():
        raise ValueError("L_ct_expression must be a nonempty string")

    r_sym = sp.Symbol("R_Sigma")
    k_sym = sp.Symbol("K_trace")
    chi_sym = sp.Symbol("chi")
    parameter_symbols = {str(key): sp.Symbol(str(key)) for key in payload.get("parameters", {})}
    parameters = {
        parameter_symbols[str(key)]: float(value)
        for key, value in payload.get("parameters", {}).items()
    }
    expr = sp.sympify(
        expression,
        locals={"R_Sigma": r_sym, "K_trace": k_sym, "chi": chi_sym, **parameter_symbols},
    )
    expr = sp.simplify(expr.subs(parameters))
    unknown = expr.free_symbols - {r_sym, k_sym, chi_sym}
    if unknown:
        names = ", ".join(sorted(str(sym) for sym in unknown))
        raise ValueError(f"Unresolved symbols in L_ct_expression: {names}")
    return expr, r_sym, k_sym, chi_sym


def build_residual_tensors_from_local_density_action(
    *,
    q_payload: dict,
    density_payload: dict,
) -> dict:
    _active(q_payload, "q_payload")
    _active(density_payload, "density_payload")
    q = np.asarray(q_payload["unit_intrinsic_metric_q_ab"], dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1] or not np.all(np.isfinite(q)):
        raise ValueError("unit_intrinsic_metric_q_ab must be a finite square tensor")
    q_inv = np.linalg.inv(q)
    dim = q.shape[0]

    a_grid = np.asarray(density_payload["a_grid"], dtype=float)
    if a_grid.ndim != 1 or a_grid.size < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(a_grid <= 0.0) or np.any(np.diff(a_grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    shape = a_grid.shape
    radius = _radius_series(density_payload, shape)
    k_trace = _series(
        density_payload,
        "K_trace_values",
        shape,
    ) if "K_trace_values" in density_payload else float(dim) / radius
    chi = _series(density_payload, "chi_values", shape) if "chi_values" in density_payload else np.zeros_like(radius)

    expr, r_sym, k_sym, chi_sym = _compile_density(density_payload)
    d_r = sp.diff(expr, r_sym)
    d_k = sp.diff(expr, k_sym)
    f_r = sp.lambdify((r_sym, k_sym, chi_sym), d_r, "numpy")(radius, k_trace, chi)
    f_k = sp.lambdify((r_sym, k_sym, chi_sym), d_k, "numpy")(radius, k_trace, chi)
    f_r = np.broadcast_to(np.asarray(f_r, dtype=float), shape)
    f_k = np.broadcast_to(np.asarray(f_k, dtype=float), shape)
    if not np.all(np.isfinite(f_r)) or not np.all(np.isfinite(f_k)):
        raise ValueError("density derivatives must be finite on the active grid")

    rh_q = -f_r / (2.0 * radius) + float(dim) * f_k / radius**3
    rk_q = -float(dim) * f_k / radius**2
    r_h = np.asarray([(value / dim) * q_inv for value in rh_q], dtype=float)
    r_k = np.asarray([(value / dim) * q_inv for value in rk_q], dtype=float)

    common = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "a_grid": a_grid.tolist(),
        "R_Sigma_values": radius.tolist(),
        "density_expression": str(expr),
        "density_expression_provenance": density_payload.get(
            "density_expression_provenance", "active local Sigma counterterm action"
        ),
        "variation_convention": "residual one-form coefficients R = -delta L_ct/delta(field)",
        "isotropic_trace_reduction": True,
    }
    return {
        "metric_payload": {
            **common,
            "R_h_ab": r_h.tolist(),
            "R_h_q_contract_values": rh_q.tolist(),
            "provenance": "active density variation: metric-scale and K_trace h-variation",
        },
        "extrinsic_payload": {
            **common,
            "R_K_ab": r_k.tolist(),
            "R_K_q_contract_values": rk_q.tolist(),
            "provenance": "active density variation: K_trace variation",
        },
        "diagnostic": {
            **common,
            "dL_dR_values": f_r.tolist(),
            "dL_dK_trace_values": f_k.tolist(),
            "R_h_q_contract_values": rh_q.tolist(),
            "R_K_q_contract_values": rk_q.tolist(),
            "formula": {
                "R_h_q": "-(partial L/partial R_Sigma)/(2 R_Sigma) + dim*(partial L/partial K_trace)/R_Sigma^3",
                "R_K_q": "-dim*(partial L/partial K_trace)/R_Sigma^2",
            },
        },
    }
