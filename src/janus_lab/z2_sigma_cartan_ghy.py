"""Cartan-GHY FLRW component builders for the active Z2/Sigma BAO path."""

from __future__ import annotations

from collections.abc import Callable

import numpy as np

from .z2_sigma_extrinsic_curvature import extrinsic_curvature_from_embedding_second_form
from .z2_sigma_extrinsic_curvature import make_z2_oriented_extrinsic_curvature_jumps
from .z2_sigma_metric_geometry import (
    christoffel_symbols_from_metric_derivatives,
    induced_metric_from_tangents,
    inverse_metric,
    normalize_level_set_normal_covector,
)
from .z2_sigma_flrw_component_manifest import FORBIDDEN_PROVENANCE_TOKENS


ArrayFn = Callable[[np.ndarray], np.ndarray]


def _finite_difference_weights_at_zero(offsets: np.ndarray) -> np.ndarray:
    if offsets.ndim != 1 or len(offsets) < 2:
        raise ValueError("radial_offsets must be one-dimensional with at least two points")
    if not np.all(np.isfinite(offsets)):
        raise ValueError("radial_offsets must be finite")
    if len(set(float(value) for value in offsets)) != len(offsets):
        raise ValueError("radial_offsets must be unique")
    if not np.any(offsets == 0.0):
        raise ValueError("radial_offsets must include 0.0")
    powers = np.arange(len(offsets), dtype=float)
    matrix = offsets[None, :] ** powers[:, None]
    rhs = np.zeros(len(offsets), dtype=float)
    rhs[1] = 1.0
    return np.linalg.solve(matrix, rhs)


def _linear_value_and_gradient_at_zero(
    coordinates: np.ndarray,
    values: np.ndarray,
    name: str,
) -> tuple[np.ndarray, np.ndarray]:
    coords = np.asarray(coordinates, dtype=float)
    vals = np.asarray(values, dtype=float)
    if coords.ndim != 2:
        raise ValueError(f"{name} coordinates must have shape (samples, dim)")
    if vals.shape[0] != coords.shape[0]:
        raise ValueError(f"{name} values must match coordinate sample count")
    if not np.all(np.isfinite(coords)) or not np.all(np.isfinite(vals)):
        raise ValueError(f"{name} samples must be finite")
    design = np.column_stack([np.ones(coords.shape[0]), coords])
    if np.linalg.matrix_rank(design) < design.shape[1]:
        raise ValueError(f"{name} samples do not determine a linear jet")
    flat = vals.reshape(vals.shape[0], -1)
    coeffs, *_ = np.linalg.lstsq(design, flat, rcond=None)
    value = coeffs[0].reshape(vals.shape[1:])
    gradient = coeffs[1:].reshape((coords.shape[1],) + vals.shape[1:])
    return value, gradient


def _quadratic_jet_at_zero(
    coordinates: np.ndarray,
    values: np.ndarray,
    name: str,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    coords = np.asarray(coordinates, dtype=float)
    vals = np.asarray(values, dtype=float)
    if coords.ndim != 2:
        raise ValueError(f"{name} coordinates must have shape (samples, dim)")
    if vals.shape[0] != coords.shape[0]:
        raise ValueError(f"{name} values must match coordinate sample count")
    if not np.all(np.isfinite(coords)) or not np.all(np.isfinite(vals)):
        raise ValueError(f"{name} samples must be finite")
    dim = coords.shape[1]
    quadratic_pairs = [(i, j) for i in range(dim) for j in range(i, dim)]
    columns = [np.ones(coords.shape[0])]
    columns.extend(coords[:, i] for i in range(dim))
    columns.extend(coords[:, i] * coords[:, j] for i, j in quadratic_pairs)
    design = np.column_stack(columns)
    if np.linalg.matrix_rank(design) < design.shape[1]:
        raise ValueError(f"{name} samples do not determine a quadratic jet")
    flat = vals.reshape(vals.shape[0], -1)
    coeffs, *_ = np.linalg.lstsq(design, flat, rcond=None)
    value = coeffs[0].reshape(vals.shape[1:])
    first = coeffs[1 : 1 + dim].reshape((dim,) + vals.shape[1:])
    second = np.zeros((dim, dim) + vals.shape[1:], dtype=float)
    start = 1 + dim
    for pair_index, (i, j) in enumerate(quadratic_pairs):
        coeff = coeffs[start + pair_index].reshape(vals.shape[1:])
        if i == j:
            second[i, j] = 2.0 * coeff
        else:
            second[i, j] = coeff
            second[j, i] = coeff
    return value, first, second


def _clean_source(source: str, field: str) -> str:
    cleaned = str(source).strip()
    if not cleaned:
        raise ValueError(f"Missing active provenance for {field}")
    lowered = cleaned.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden provenance for {field}: {cleaned}")
    return cleaned


def _checked_array(values, shape: tuple[int, ...], name: str) -> np.ndarray:
    array = np.asarray(values, dtype=float)
    if array.shape != shape:
        raise ValueError(f"{name} returned shape {array.shape}, expected {shape}")
    if not np.all(np.isfinite(array)):
        raise ValueError(f"{name} returned non-finite values")
    return array


def make_cartan_ghy_components_over_rho_crit0(
    delta_k_s_of_a: ArrayFn,
    delta_k_tau_of_a: ArrayFn,
    *,
    z2_orientation_sign: float,
    kappa_rho_crit0: float,
) -> tuple[ArrayFn, ArrayFn]:
    """Return active Cartan-GHY rho/p components on an `a` grid.

    Formulas:
    rho_CGHY = 3 eps_Z2 DeltaK_s / kappa
    p_CGHY = eps_Z2 (DeltaK_tau - 2 DeltaK_s) / kappa

    The returned quantities are divided by rho_crit0. No H0 or Planck/LCDM
    normalization is inferred here.
    """

    if z2_orientation_sign not in (-1.0, 1.0):
        raise ValueError("z2_orientation_sign must be +1.0 or -1.0")
    if kappa_rho_crit0 <= 0.0:
        raise ValueError("kappa_rho_crit0 must be positive")

    eps = float(z2_orientation_sign)
    norm = float(kappa_rho_crit0)

    def rho(a: np.ndarray) -> np.ndarray:
        grid = np.asarray(a, dtype=float)
        delta_k_s = _checked_array(delta_k_s_of_a(grid), grid.shape, "delta_k_s_of_a")
        return 3.0 * eps * delta_k_s / norm

    def pressure(a: np.ndarray) -> np.ndarray:
        grid = np.asarray(a, dtype=float)
        delta_k_s = _checked_array(delta_k_s_of_a(grid), grid.shape, "delta_k_s_of_a")
        delta_k_tau = _checked_array(delta_k_tau_of_a(grid), grid.shape, "delta_k_tau_of_a")
        return eps * (delta_k_tau - 2.0 * delta_k_s) / norm

    return rho, pressure


def make_cartan_ghy_components_from_plus_minus_extrinsic_curvature(
    k_s_plus_of_a: ArrayFn,
    k_s_minus_of_a: ArrayFn,
    k_tau_plus_of_a: ArrayFn,
    k_tau_minus_of_a: ArrayFn,
    *,
    z2_orientation_sign: float,
    kappa_rho_crit0: float,
) -> tuple[ArrayFn, ArrayFn]:
    """Compose active K^pm(a) -> DeltaK(a) -> Cartan-GHY rho/p components."""

    delta_k_s, delta_k_tau = make_z2_oriented_extrinsic_curvature_jumps(
        k_s_plus_of_a,
        k_s_minus_of_a,
        k_tau_plus_of_a,
        k_tau_minus_of_a,
        z2_orientation_sign=z2_orientation_sign,
    )
    return make_cartan_ghy_components_over_rho_crit0(
        delta_k_s,
        delta_k_tau,
        z2_orientation_sign=z2_orientation_sign,
        kappa_rho_crit0=kappa_rho_crit0,
    )


def build_cartan_ghy_component_payload(
    *,
    a_grid: list[float] | np.ndarray,
    delta_k_s: list[float] | np.ndarray,
    delta_k_tau: list[float] | np.ndarray,
    z2_orientation_sign: float,
    kappa_rho_crit0: float,
    component_provenance: str,
) -> dict:
    """Build active Cartan-GHY rho/p arrays from DeltaK and critical normalization."""

    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    delta_s = _checked_array(delta_k_s, grid.shape, "delta_k_s")
    delta_tau = _checked_array(delta_k_tau, grid.shape, "delta_k_tau")
    provenance = _clean_source(component_provenance, "cartan_ghy")
    rho, pressure = make_cartan_ghy_components_over_rho_crit0(
        lambda a: np.interp(a, grid, delta_s),
        lambda a: np.interp(a, grid, delta_tau),
        z2_orientation_sign=z2_orientation_sign,
        kappa_rho_crit0=kappa_rho_crit0,
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "component_route": "cartan_ghy_from_active_deltaK",
        "a_grid": grid.tolist(),
        "flrw_components_over_rho_crit0": {
            "cartan_ghy_rho": rho(grid).tolist(),
            "cartan_ghy_p": pressure(grid).tolist(),
        },
        "component_provenance": {
            "cartan_ghy_rho": provenance,
            "cartan_ghy_p": provenance,
        },
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
    }


def build_cartan_ghy_deltaK_input_payload(
    *,
    a_grid: list[float] | np.ndarray,
    k_s_plus: list[float] | np.ndarray,
    k_s_minus: list[float] | np.ndarray,
    k_tau_plus: list[float] | np.ndarray,
    k_tau_minus: list[float] | np.ndarray,
    z2_orientation_sign: float,
    deltaK_provenance: str,
) -> dict:
    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    ks_plus = _checked_array(k_s_plus, grid.shape, "k_s_plus")
    ks_minus = _checked_array(k_s_minus, grid.shape, "k_s_minus")
    kt_plus = _checked_array(k_tau_plus, grid.shape, "k_tau_plus")
    kt_minus = _checked_array(k_tau_minus, grid.shape, "k_tau_minus")
    provenance = _clean_source(deltaK_provenance, "DeltaK")
    delta_s, delta_tau = make_z2_oriented_extrinsic_curvature_jumps(
        lambda a: np.interp(a, grid, ks_plus),
        lambda a: np.interp(a, grid, ks_minus),
        lambda a: np.interp(a, grid, kt_plus),
        lambda a: np.interp(a, grid, kt_minus),
        z2_orientation_sign=z2_orientation_sign,
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": grid.tolist(),
        "DeltaK_s_Z2Sigma": delta_s(grid).tolist(),
        "DeltaK_tau_Z2Sigma": delta_tau(grid).tolist(),
        "z2_orientation_sign": float(z2_orientation_sign),
        "DeltaK_provenance": provenance,
    }


def build_cartan_ghy_rsigma_radial_term_input_payload(
    *,
    a_grid: list[float] | np.ndarray,
    sqrt_abs_h: list[float] | np.ndarray,
    K_trace: list[float] | np.ndarray,
    partial_R_K_trace: list[float] | np.ndarray,
    trace_h_inv_partial_R_h: list[float] | np.ndarray,
    z2_orientation_sign: float,
    kappa_Z2Sigma: float,
    term_provenance: str,
) -> dict:
    """Build the active Cartan-GHY radial variation term for the R_Sigma equation."""

    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    if z2_orientation_sign not in (-1.0, 1.0):
        raise ValueError("z2_orientation_sign must be +1.0 or -1.0")
    if kappa_Z2Sigma <= 0.0:
        raise ValueError("kappa_Z2Sigma must be positive")

    sqrt_h = _checked_array(sqrt_abs_h, grid.shape, "sqrt_abs_h")
    if np.any(sqrt_h <= 0.0):
        raise ValueError("sqrt_abs_h must be strictly positive")
    k_trace = _checked_array(K_trace, grid.shape, "K_trace")
    partial_k = _checked_array(partial_R_K_trace, grid.shape, "partial_R_K_trace")
    trace_h = _checked_array(
        trace_h_inv_partial_R_h,
        grid.shape,
        "trace_h_inv_partial_R_h",
    )
    provenance = _clean_source(term_provenance, "E_CartanGHY")

    eps = float(z2_orientation_sign)
    kappa = float(kappa_Z2Sigma)
    values = eps * sqrt_h * (partial_k + 0.5 * k_trace * trace_h) / kappa

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "radial_embedding_variation_evaluated": True,
        "a_grid": grid.tolist(),
        "E_CartanGHY": values.tolist(),
        "E_CartanGHY_provenance": provenance,
        "cartan_ghy_radial_formula": (
            "eps_Z2/kappa * sqrt_abs_h * "
            "(partial_R_K + 1/2 K trace_h_inv_partial_R_h)"
        ),
    }


def build_cartan_ghy_rsigma_radial_variation_primitives_payload(
    *,
    a_grid: list[float] | np.ndarray,
    induced_metric_h_ab: list | np.ndarray,
    partial_R_induced_metric_h_ab: list | np.ndarray,
    extrinsic_curvature_K_ab: list | np.ndarray,
    partial_R_extrinsic_curvature_K_ab: list | np.ndarray,
    z2_orientation_sign: float,
    kappa_Z2Sigma: float,
    term_provenance: str,
) -> dict:
    """Reduce h_ab, partial_R h_ab, K_ab and partial_R K_ab to radial inputs."""

    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    if z2_orientation_sign not in (-1.0, 1.0):
        raise ValueError("z2_orientation_sign must be +1.0 or -1.0")
    if kappa_Z2Sigma <= 0.0:
        raise ValueError("kappa_Z2Sigma must be positive")
    h = np.asarray(induced_metric_h_ab, dtype=float)
    if h.ndim != 3 or h.shape[0] != len(grid) or h.shape[1] != h.shape[2]:
        raise ValueError("induced_metric_h_ab must have shape (len(a_grid), d, d)")
    shape = h.shape
    dh = _checked_array(partial_R_induced_metric_h_ab, shape, "partial_R_induced_metric_h_ab")
    k = _checked_array(extrinsic_curvature_K_ab, shape, "extrinsic_curvature_K_ab")
    dk = _checked_array(
        partial_R_extrinsic_curvature_K_ab,
        shape,
        "partial_R_extrinsic_curvature_K_ab",
    )

    sqrt_abs_h: list[float] = []
    k_trace: list[float] = []
    partial_k_trace: list[float] = []
    trace_h_inv_dh: list[float] = []
    for index in range(len(grid)):
        h_i = h[index]
        if not np.allclose(h_i, h_i.T):
            raise ValueError("induced_metric_h_ab must be symmetric")
        det_h = float(np.linalg.det(h_i))
        if det_h == 0.0 or not np.isfinite(det_h):
            raise ValueError("induced_metric_h_ab must be nondegenerate")
        h_inv = np.linalg.inv(h_i)
        sqrt_abs_h.append(float(np.sqrt(abs(det_h))))
        k_trace.append(float(np.einsum("ab,ab->", h_inv, k[index])))
        trace_dh = float(np.einsum("ab,ab->", h_inv, dh[index]))
        trace_h_inv_dh.append(trace_dh)
        inverse_variation_term = float(
            np.einsum("ac,cd,db,ab->", h_inv, dh[index], h_inv, k[index])
        )
        direct_k_term = float(np.einsum("ab,ab->", h_inv, dk[index]))
        partial_k_trace.append(direct_k_term - inverse_variation_term)

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": grid.tolist(),
        "sqrt_abs_h": sqrt_abs_h,
        "K_trace": k_trace,
        "partial_R_K_trace": partial_k_trace,
        "trace_h_inv_partial_R_h": trace_h_inv_dh,
        "z2_orientation_sign": float(z2_orientation_sign),
        "kappa_Z2Sigma": float(kappa_Z2Sigma),
        "E_CartanGHY_provenance": _clean_source(term_provenance, "E_CartanGHY"),
        "partial_R_K_trace_definition": "partial_R(h^{ab} K_ab)",
    }


def build_cartan_ghy_rsigma_radial_tensor_primitives_from_embedding_stencil_payload(
    *,
    a_grid: list[float] | np.ndarray,
    radial_offsets: list[float] | np.ndarray,
    metric_covariant_stencil: list | np.ndarray,
    tangent_vectors_stencil: list | np.ndarray,
    second_embedding_stencil: list | np.ndarray,
    christoffels_stencil: list | np.ndarray,
    normal_covector_stencil: list | np.ndarray,
    z2_orientation_sign: float,
    kappa_Z2Sigma: float,
    term_provenance: str,
) -> dict:
    """Compute h_ab, partial_R h_ab, K_ab and partial_R K_ab from a radial stencil."""

    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    offsets = np.asarray(radial_offsets, dtype=float)
    weights = _finite_difference_weights_at_zero(offsets)
    zero_index = int(np.where(offsets == 0.0)[0][0])

    metric = np.asarray(metric_covariant_stencil, dtype=float)
    tangents = np.asarray(tangent_vectors_stencil, dtype=float)
    second = np.asarray(second_embedding_stencil, dtype=float)
    gamma = np.asarray(christoffels_stencil, dtype=float)
    normal = np.asarray(normal_covector_stencil, dtype=float)
    if metric.ndim != 4 or metric.shape[:2] != (len(grid), len(offsets)):
        raise ValueError("metric_covariant_stencil must have shape (a, radial, ambient, ambient)")
    if tangents.ndim != 4 or tangents.shape[:2] != (len(grid), len(offsets)):
        raise ValueError("tangent_vectors_stencil must have shape (a, radial, intrinsic, ambient)")
    if second.ndim != 5 or second.shape[:2] != (len(grid), len(offsets)):
        raise ValueError(
            "second_embedding_stencil must have shape (a, radial, intrinsic, intrinsic, ambient)"
        )
    if gamma.ndim != 5 or gamma.shape[:2] != (len(grid), len(offsets)):
        raise ValueError("christoffels_stencil must have shape (a, radial, ambient, ambient, ambient)")
    if normal.ndim != 3 or normal.shape[:2] != (len(grid), len(offsets)):
        raise ValueError("normal_covector_stencil must have shape (a, radial, ambient)")

    h_stencil: list[list[np.ndarray]] = []
    k_stencil: list[list[np.ndarray]] = []
    for a_index in range(len(grid)):
        h_row: list[np.ndarray] = []
        k_row: list[np.ndarray] = []
        for r_index in range(len(offsets)):
            h_row.append(induced_metric_from_tangents(metric[a_index, r_index], tangents[a_index, r_index]))
            k_row.append(
                extrinsic_curvature_from_embedding_second_form(
                    tangents[a_index, r_index],
                    second[a_index, r_index],
                    gamma[a_index, r_index],
                    normal[a_index, r_index],
                )
            )
        h_stencil.append(h_row)
        k_stencil.append(k_row)

    h0 = np.asarray([row[zero_index] for row in h_stencil], dtype=float)
    k0 = np.asarray([row[zero_index] for row in k_stencil], dtype=float)
    partial_h = np.asarray(
        [sum(weights[j] * row[j] for j in range(len(offsets))) for row in h_stencil],
        dtype=float,
    )
    partial_k = np.asarray(
        [sum(weights[j] * row[j] for j in range(len(offsets))) for row in k_stencil],
        dtype=float,
    )

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": grid.tolist(),
        "induced_metric_h_ab": h0.tolist(),
        "partial_R_induced_metric_h_ab": partial_h.tolist(),
        "extrinsic_curvature_K_ab": k0.tolist(),
        "partial_R_extrinsic_curvature_K_ab": partial_k.tolist(),
        "z2_orientation_sign": float(z2_orientation_sign),
        "kappa_Z2Sigma": float(kappa_Z2Sigma),
        "E_CartanGHY_provenance": _clean_source(term_provenance, "E_CartanGHY"),
        "radial_offsets": offsets.tolist(),
        "radial_derivative_weights_at_sigma": weights.tolist(),
        "tensor_primitive_route": "embedding_radial_stencil",
    }


def build_cartan_ghy_rsigma_embedding_stencil_from_chart_payload(
    *,
    a_grid: list[float] | np.ndarray,
    radial_offsets: list[float] | np.ndarray,
    metric_covariant_stencil: list | np.ndarray,
    metric_derivatives_stencil: list | np.ndarray,
    tangent_vectors_stencil: list | np.ndarray,
    second_embedding_stencil: list | np.ndarray,
    level_gradient_covector_stencil: list | np.ndarray,
    normal_norm_sign: float,
    orientation_sign: float,
    z2_orientation_sign: float,
    kappa_Z2Sigma: float,
    term_provenance: str,
) -> dict:
    """Compute Christoffels and unit normals for the embedding radial stencil."""

    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    offsets = np.asarray(radial_offsets, dtype=float)
    _finite_difference_weights_at_zero(offsets)
    metric = np.asarray(metric_covariant_stencil, dtype=float)
    dg = np.asarray(metric_derivatives_stencil, dtype=float)
    tangents = np.asarray(tangent_vectors_stencil, dtype=float)
    second = np.asarray(second_embedding_stencil, dtype=float)
    level_grad = np.asarray(level_gradient_covector_stencil, dtype=float)
    if metric.ndim != 4 or metric.shape[:2] != (len(grid), len(offsets)):
        raise ValueError("metric_covariant_stencil must have shape (a, radial, ambient, ambient)")
    ambient_dim = metric.shape[-1]
    if metric.shape[-2] != ambient_dim:
        raise ValueError("metric_covariant_stencil must contain square metrics")
    if dg.shape != (len(grid), len(offsets), ambient_dim, ambient_dim, ambient_dim):
        raise ValueError("metric_derivatives_stencil must have shape (a, radial, ambient, ambient, ambient)")
    if tangents.ndim != 4 or tangents.shape[:2] != (len(grid), len(offsets)):
        raise ValueError("tangent_vectors_stencil must have shape (a, radial, intrinsic, ambient)")
    intrinsic_dim = tangents.shape[-2]
    if tangents.shape[-1] != ambient_dim:
        raise ValueError("tangent_vectors_stencil ambient dimension mismatch")
    if second.shape != (len(grid), len(offsets), intrinsic_dim, intrinsic_dim, ambient_dim):
        raise ValueError(
            "second_embedding_stencil must have shape (a, radial, intrinsic, intrinsic, ambient)"
        )
    if level_grad.shape != (len(grid), len(offsets), ambient_dim):
        raise ValueError("level_gradient_covector_stencil must have shape (a, radial, ambient)")

    christoffels = []
    normals = []
    for a_index in range(len(grid)):
        gamma_row = []
        normal_row = []
        for r_index in range(len(offsets)):
            inv = inverse_metric(metric[a_index, r_index])
            gamma_row.append(christoffel_symbols_from_metric_derivatives(inv, dg[a_index, r_index]))
            normal_row.append(
                normalize_level_set_normal_covector(
                    level_grad[a_index, r_index],
                    inv,
                    normal_norm_sign=normal_norm_sign,
                    orientation_sign=orientation_sign,
                )
            )
        christoffels.append(gamma_row)
        normals.append(normal_row)

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": grid.tolist(),
        "radial_offsets": offsets.tolist(),
        "metric_covariant_stencil": metric.tolist(),
        "tangent_vectors_stencil": tangents.tolist(),
        "second_embedding_stencil": second.tolist(),
        "christoffels_stencil": np.asarray(christoffels, dtype=float).tolist(),
        "normal_covector_stencil": np.asarray(normals, dtype=float).tolist(),
        "z2_orientation_sign": float(z2_orientation_sign),
        "kappa_Z2Sigma": float(kappa_Z2Sigma),
        "E_CartanGHY_provenance": _clean_source(term_provenance, "E_CartanGHY"),
        "normal_norm_sign": float(normal_norm_sign),
        "orientation_sign": float(orientation_sign),
        "embedding_stencil_route": "chart_metric_derivatives_level_set",
    }


def build_cartan_ghy_rsigma_chart_stencil_from_sampled_local_chart_payload(
    *,
    a_grid: list[float] | np.ndarray,
    radial_offsets: list[float] | np.ndarray,
    ambient_coordinate_offsets: list | np.ndarray,
    intrinsic_coordinate_offsets: list | np.ndarray,
    metric_covariant_samples: list | np.ndarray,
    level_set_samples: list | np.ndarray,
    embedding_coordinate_samples: list | np.ndarray,
    normal_norm_sign: float,
    orientation_sign: float,
    z2_orientation_sign: float,
    kappa_Z2Sigma: float,
    term_provenance: str,
) -> dict:
    """Build chart stencils from local ambient/intrinsic coordinate samples."""

    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    offsets = np.asarray(radial_offsets, dtype=float)
    _finite_difference_weights_at_zero(offsets)
    ambient_offsets = np.asarray(ambient_coordinate_offsets, dtype=float)
    intrinsic_offsets = np.asarray(intrinsic_coordinate_offsets, dtype=float)
    metric_samples = np.asarray(metric_covariant_samples, dtype=float)
    level_samples = np.asarray(level_set_samples, dtype=float)
    embedding_samples = np.asarray(embedding_coordinate_samples, dtype=float)

    if ambient_offsets.ndim != 2:
        raise ValueError("ambient_coordinate_offsets must have shape (samples, ambient)")
    if intrinsic_offsets.ndim != 2:
        raise ValueError("intrinsic_coordinate_offsets must have shape (samples, intrinsic)")
    ambient_dim = ambient_offsets.shape[1]
    intrinsic_dim = intrinsic_offsets.shape[1]
    if metric_samples.shape != (
        len(grid),
        len(offsets),
        len(ambient_offsets),
        ambient_dim,
        ambient_dim,
    ):
        raise ValueError("metric_covariant_samples must have shape (a, radial, ambient_samples, ambient, ambient)")
    if level_samples.shape != (len(grid), len(offsets), len(ambient_offsets)):
        raise ValueError("level_set_samples must have shape (a, radial, ambient_samples)")
    if embedding_samples.shape != (
        len(grid),
        len(offsets),
        len(intrinsic_offsets),
        ambient_dim,
    ):
        raise ValueError("embedding_coordinate_samples must have shape (a, radial, intrinsic_samples, ambient)")

    metrics = []
    metric_derivatives = []
    level_gradients = []
    tangents = []
    second_embeddings = []
    for a_index in range(len(grid)):
        metric_row = []
        metric_derivative_row = []
        gradient_row = []
        tangent_row = []
        second_row = []
        for r_index in range(len(offsets)):
            metric_value, metric_gradient, _metric_second = _quadratic_jet_at_zero(
                ambient_offsets,
                metric_samples[a_index, r_index],
                "metric_covariant_samples",
            )
            _level_value, level_gradient = _linear_value_and_gradient_at_zero(
                ambient_offsets,
                level_samples[a_index, r_index],
                "level_set_samples",
            )
            _embedding_value, first, second = _quadratic_jet_at_zero(
                intrinsic_offsets,
                embedding_samples[a_index, r_index],
                "embedding_coordinate_samples",
            )
            metric_row.append(metric_value)
            metric_derivative_row.append(metric_gradient)
            gradient_row.append(level_gradient)
            tangent_row.append(first)
            second_row.append(second)
        metrics.append(metric_row)
        metric_derivatives.append(metric_derivative_row)
        level_gradients.append(gradient_row)
        tangents.append(tangent_row)
        second_embeddings.append(second_row)

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": grid.tolist(),
        "radial_offsets": offsets.tolist(),
        "metric_covariant_stencil": np.asarray(metrics, dtype=float).tolist(),
        "metric_derivatives_stencil": np.asarray(metric_derivatives, dtype=float).tolist(),
        "tangent_vectors_stencil": np.asarray(tangents, dtype=float).tolist(),
        "second_embedding_stencil": np.asarray(second_embeddings, dtype=float).tolist(),
        "level_gradient_covector_stencil": np.asarray(level_gradients, dtype=float).tolist(),
        "normal_norm_sign": float(normal_norm_sign),
        "orientation_sign": float(orientation_sign),
        "z2_orientation_sign": float(z2_orientation_sign),
        "kappa_Z2Sigma": float(kappa_Z2Sigma),
        "E_CartanGHY_provenance": _clean_source(term_provenance, "E_CartanGHY"),
        "chart_stencil_route": "sampled_local_chart_jets",
        "ambient_coordinate_offsets": ambient_offsets.tolist(),
        "intrinsic_coordinate_offsets": intrinsic_offsets.tolist(),
    }


def build_cartan_ghy_rsigma_local_chart_from_gaussian_collar_payload(
    *,
    a_grid: list[float] | np.ndarray,
    radial_offsets: list[float] | np.ndarray,
    ambient_coordinate_offsets: list | np.ndarray,
    intrinsic_coordinate_offsets: list | np.ndarray,
    induced_metric_h_ab: list | np.ndarray,
    partial_R_induced_metric_h_ab: list | np.ndarray,
    partial_R2_induced_metric_h_ab: list | np.ndarray,
    z2_orientation_sign: float,
    kappa_Z2Sigma: float,
    term_provenance: str,
) -> dict:
    """Generate local chart samples from a Gaussian-normal collar Taylor expansion."""

    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    radial = np.asarray(radial_offsets, dtype=float)
    _finite_difference_weights_at_zero(radial)
    ambient_offsets = np.asarray(ambient_coordinate_offsets, dtype=float)
    intrinsic_offsets = np.asarray(intrinsic_coordinate_offsets, dtype=float)
    h0 = np.asarray(induced_metric_h_ab, dtype=float)
    dh = np.asarray(partial_R_induced_metric_h_ab, dtype=float)
    d2h = np.asarray(partial_R2_induced_metric_h_ab, dtype=float)
    if h0.ndim != 3 or h0.shape[0] != len(grid) or h0.shape[1] != h0.shape[2]:
        raise ValueError("induced_metric_h_ab must have shape (a, intrinsic, intrinsic)")
    if dh.shape != h0.shape:
        raise ValueError("partial_R_induced_metric_h_ab must match induced_metric_h_ab shape")
    if d2h.shape != h0.shape:
        raise ValueError("partial_R2_induced_metric_h_ab must match induced_metric_h_ab shape")
    intrinsic_dim = h0.shape[1]
    ambient_dim = intrinsic_dim + 1
    if ambient_offsets.ndim != 2 or ambient_offsets.shape[1] != ambient_dim:
        raise ValueError("ambient_coordinate_offsets must have shape (samples, intrinsic_dim + 1)")
    if intrinsic_offsets.ndim != 2 or intrinsic_offsets.shape[1] != intrinsic_dim:
        raise ValueError("intrinsic_coordinate_offsets must have shape (samples, intrinsic_dim)")

    metric_samples = []
    level_samples = []
    embedding_samples = []
    for a_index in range(len(grid)):
        if not np.allclose(h0[a_index], h0[a_index].T):
            raise ValueError("induced_metric_h_ab must be symmetric")
        if np.linalg.det(h0[a_index]) == 0.0:
            raise ValueError("induced_metric_h_ab must be nondegenerate")
        metric_radial = []
        level_radial = []
        embedding_radial = []
        for radial_value in radial:
            metric_row = []
            level_row = []
            for ambient_offset in ambient_offsets:
                normal_coordinate = float(radial_value + ambient_offset[0])
                h = h0[a_index] + normal_coordinate * dh[a_index] + 0.5 * normal_coordinate**2 * d2h[a_index]
                metric = np.zeros((ambient_dim, ambient_dim), dtype=float)
                metric[0, 0] = 1.0
                metric[1:, 1:] = h
                metric_row.append(metric.tolist())
                level_row.append(float(ambient_offset[0]))
            embedding_row = []
            for intrinsic_offset in intrinsic_offsets:
                embedding_row.append([float(radial_value), *[float(x) for x in intrinsic_offset]])
            metric_radial.append(metric_row)
            level_radial.append(level_row)
            embedding_radial.append(embedding_row)
        metric_samples.append(metric_radial)
        level_samples.append(level_radial)
        embedding_samples.append(embedding_radial)

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": grid.tolist(),
        "radial_offsets": radial.tolist(),
        "ambient_coordinate_offsets": ambient_offsets.tolist(),
        "intrinsic_coordinate_offsets": intrinsic_offsets.tolist(),
        "metric_covariant_samples": metric_samples,
        "level_set_samples": level_samples,
        "embedding_coordinate_samples": embedding_samples,
        "normal_norm_sign": 1.0,
        "orientation_sign": 1.0,
        "z2_orientation_sign": float(z2_orientation_sign),
        "kappa_Z2Sigma": float(kappa_Z2Sigma),
        "E_CartanGHY_provenance": _clean_source(term_provenance, "E_CartanGHY"),
        "local_chart_route": "gaussian_collar_taylor_h_dh_d2h",
    }


def build_cartan_ghy_rsigma_gaussian_collar_from_isotropic_radius_payload(
    *,
    a_grid: list[float] | np.ndarray,
    R_Sigma_of_a: list[float] | np.ndarray,
    unit_intrinsic_metric_q_ab: list | np.ndarray,
    radial_offsets: list[float] | np.ndarray,
    ambient_coordinate_offsets: list | np.ndarray,
    intrinsic_coordinate_offsets: list | np.ndarray,
    z2_orientation_sign: float,
    kappa_Z2Sigma: float,
    term_provenance: str,
) -> dict:
    """Build Gaussian-collar h, dR h, dR2 h from isotropic throat radius."""

    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    radius = _checked_array(R_Sigma_of_a, grid.shape, "R_Sigma_of_a")
    if np.any(radius <= 0.0):
        raise ValueError("R_Sigma_of_a must be strictly positive")
    q = np.asarray(unit_intrinsic_metric_q_ab, dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1]:
        raise ValueError("unit_intrinsic_metric_q_ab must be square")
    if not np.allclose(q, q.T):
        raise ValueError("unit_intrinsic_metric_q_ab must be symmetric")
    if np.linalg.det(q) == 0.0:
        raise ValueError("unit_intrinsic_metric_q_ab must be nondegenerate")

    h = np.asarray([float(r) ** 2 * q for r in radius], dtype=float)
    dh = np.asarray([2.0 * float(r) * q for r in radius], dtype=float)
    d2h = np.asarray([2.0 * q for _r in radius], dtype=float)

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": grid.tolist(),
        "radial_offsets": list(radial_offsets),
        "ambient_coordinate_offsets": list(ambient_coordinate_offsets),
        "intrinsic_coordinate_offsets": list(intrinsic_coordinate_offsets),
        "induced_metric_h_ab": h.tolist(),
        "partial_R_induced_metric_h_ab": dh.tolist(),
        "partial_R2_induced_metric_h_ab": d2h.tolist(),
        "z2_orientation_sign": float(z2_orientation_sign),
        "kappa_Z2Sigma": float(kappa_Z2Sigma),
        "E_CartanGHY_provenance": _clean_source(term_provenance, "E_CartanGHY"),
        "gaussian_collar_route": "isotropic_radius_RSigma_squared_unit_metric",
    }
