"""Surface h/K variation helpers for active Z2/Sigma throat calculations."""

from __future__ import annotations

import numpy as np


def _checked(values, shape: tuple[int, ...], name: str) -> np.ndarray:
    array = np.asarray(values, dtype=float)
    if array.shape != shape:
        raise ValueError(f"{name} has shape {array.shape}, expected {shape}")
    if not np.all(np.isfinite(array)):
        raise ValueError(f"{name} contains non-finite values")
    return array


def surface_hk_alpha_radial_from_isotropic_components(
    *,
    sqrt_abs_h,
    alpha_h_tau,
    alpha_h_s,
    alpha_k_tau,
    alpha_k_s,
    partial_R_h_tau,
    partial_R_h_s,
    partial_R_K_tau,
    partial_R_K_s,
) -> np.ndarray:
    """Contract isotropic h/K alpha coefficients with radial variations.

    The 3 factor is the spatial trace degeneracy on the isotropic Sigma throat.
    """

    measure = np.asarray(sqrt_abs_h, dtype=float)
    if measure.ndim != 1:
        raise ValueError("sqrt_abs_h must be one-dimensional")
    shape = measure.shape
    if np.any(measure <= 0.0) or not np.all(np.isfinite(measure)):
        raise ValueError("sqrt_abs_h must be positive and finite")
    ah_tau = _checked(alpha_h_tau, shape, "alpha_h_tau")
    ah_s = _checked(alpha_h_s, shape, "alpha_h_s")
    ak_tau = _checked(alpha_k_tau, shape, "alpha_k_tau")
    ak_s = _checked(alpha_k_s, shape, "alpha_k_s")
    dh_tau = _checked(partial_R_h_tau, shape, "partial_R_h_tau")
    dh_s = _checked(partial_R_h_s, shape, "partial_R_h_s")
    dk_tau = _checked(partial_R_K_tau, shape, "partial_R_K_tau")
    dk_s = _checked(partial_R_K_s, shape, "partial_R_K_s")
    return measure * (
        ah_tau * dh_tau
        + 3.0 * ah_s * dh_s
        + ak_tau * dk_tau
        + 3.0 * ak_s * dk_s
    )


def polynomial_surface_hk_isotropic_alpha_components(
    *,
    a0,
    a1,
    a2,
    a3,
    K_tau,
    K_s,
) -> dict[str, np.ndarray]:
    """Evaluate isotropic alpha components for L=a0+a1*K+a2*K^2+a3*K_ab K^ab.

    Conventions: mostly-plus induced metric, K = -K_tau + 3*K_s, and
    K_ab K^ab = K_tau^2 + 3*K_s^2 in the orthonormal isotropic frame.
    """

    kt = np.asarray(K_tau, dtype=float)
    ks = np.asarray(K_s, dtype=float)
    if kt.shape != ks.shape:
        raise ValueError("K_tau and K_s must have matching shapes")
    if not np.all(np.isfinite(kt)) or not np.all(np.isfinite(ks)):
        raise ValueError("K_tau and K_s must be finite")
    shape = kt.shape
    c0 = _checked(np.broadcast_to(np.asarray(a0, dtype=float), shape), shape, "a0")
    c1 = _checked(np.broadcast_to(np.asarray(a1, dtype=float), shape), shape, "a1")
    c2 = _checked(np.broadcast_to(np.asarray(a2, dtype=float), shape), shape, "a2")
    c3 = _checked(np.broadcast_to(np.asarray(a3, dtype=float), shape), shape, "a3")
    trace = -kt + 3.0 * ks
    k2 = kt * kt + 3.0 * ks * ks
    density = c0 + c1 * trace + c2 * trace * trace + c3 * k2
    common = c1 + 2.0 * c2 * trace
    return {
        "K_trace": trace,
        "K_ab_Kab": k2,
        "L_Sigma": density,
        "alpha_K_tau": -c1 - 2.0 * c2 * trace + 2.0 * c3 * kt,
        "alpha_K_s": c1 + 2.0 * c2 * trace + 2.0 * c3 * ks,
        "alpha_h_tau": -0.5 * density - common * kt + 2.0 * c3 * kt * kt,
        "alpha_h_s": 0.5 * density - common * ks - 2.0 * c3 * ks * ks,
    }


def reduce_surface_hk_radial_geometry_tensors(
    *,
    induced_metric_h_ab,
    extrinsic_curvature_K_ab,
    partial_R_induced_metric_h_ab,
    partial_R_extrinsic_curvature_K_ab,
    tau_index: int = 0,
    spatial_indices: tuple[int, int, int] = (1, 2, 3),
) -> dict[str, np.ndarray]:
    """Reduce active Sigma tensors to isotropic tau/spatial components."""

    h = np.asarray(induced_metric_h_ab, dtype=float)
    if h.ndim != 3 or h.shape[1] != h.shape[2]:
        raise ValueError("induced_metric_h_ab must have shape (n,d,d)")
    shape = h.shape
    k = _checked(extrinsic_curvature_K_ab, shape, "extrinsic_curvature_K_ab")
    dh = _checked(partial_R_induced_metric_h_ab, shape, "partial_R_induced_metric_h_ab")
    dk = _checked(partial_R_extrinsic_curvature_K_ab, shape, "partial_R_extrinsic_curvature_K_ab")
    dim = h.shape[1]
    if tau_index < 0 or tau_index >= dim:
        raise ValueError("tau_index out of range")
    if len(spatial_indices) != 3 or any(index < 0 or index >= dim for index in spatial_indices):
        raise ValueError("spatial_indices must contain three valid indices")

    sqrt_abs_h: list[float] = []
    k_tau: list[float] = []
    k_s: list[float] = []
    dh_tau: list[float] = []
    dh_s: list[float] = []
    dk_tau: list[float] = []
    dk_s: list[float] = []
    for index in range(h.shape[0]):
        h_i = h[index]
        if not np.allclose(h_i, h_i.T):
            raise ValueError("induced_metric_h_ab must be symmetric")
        det_h = float(np.linalg.det(h_i))
        if det_h == 0.0 or not np.isfinite(det_h):
            raise ValueError("induced_metric_h_ab must be nondegenerate")
        spatial = h_i[np.ix_(spatial_indices, spatial_indices)]
        spatial_inv = np.linalg.inv(spatial)
        sqrt_abs_h.append(float(np.sqrt(abs(det_h))))
        k_tau.append(float(k[index, tau_index, tau_index]))
        dh_tau.append(float(dh[index, tau_index, tau_index]))
        dk_tau.append(float(dk[index, tau_index, tau_index]))
        k_spatial = k[index][np.ix_(spatial_indices, spatial_indices)]
        dh_spatial = dh[index][np.ix_(spatial_indices, spatial_indices)]
        dk_spatial = dk[index][np.ix_(spatial_indices, spatial_indices)]
        k_s.append(float(np.einsum("ij,ij->", spatial_inv, k_spatial) / 3.0))
        dh_s.append(float(np.einsum("ij,ij->", spatial_inv, dh_spatial) / 3.0))
        dk_s.append(float(np.einsum("ij,ij->", spatial_inv, dk_spatial) / 3.0))

    return {
        "sqrt_abs_h_values": np.asarray(sqrt_abs_h),
        "K_tau_values": np.asarray(k_tau),
        "K_s_values": np.asarray(k_s),
        "partial_R_h_tau_values": np.asarray(dh_tau),
        "partial_R_h_s_values": np.asarray(dh_s),
        "partial_R_K_tau_values": np.asarray(dk_tau),
        "partial_R_K_s_values": np.asarray(dk_s),
    }


def riccati_normal_flow_radial_primitives(
    *,
    induced_metric_h_ab,
    extrinsic_curvature_K_ab,
    normal_riemann_R_nabn,
) -> dict[str, np.ndarray]:
    """Compute proper-normal radial primitives from Riccati normal flow.

    Convention used by the active surface h/K gates:
    partial_R h_ab = 2 K_ab,
    partial_R K_ab = R_nabn_ab + K_a^c K_cb.
    """

    h = np.asarray(induced_metric_h_ab, dtype=float)
    if h.ndim != 3 or h.shape[1] != h.shape[2]:
        raise ValueError("induced_metric_h_ab must have shape (n,d,d)")
    shape = h.shape
    k = _checked(extrinsic_curvature_K_ab, shape, "extrinsic_curvature_K_ab")
    r = _checked(normal_riemann_R_nabn, shape, "normal_riemann_R_nabn")
    dh = 2.0 * k
    dk = []
    for index in range(h.shape[0]):
        h_i = h[index]
        if not np.allclose(h_i, h_i.T):
            raise ValueError("induced_metric_h_ab must be symmetric")
        det_h = float(np.linalg.det(h_i))
        if det_h == 0.0 or not np.isfinite(det_h):
            raise ValueError("induced_metric_h_ab must be nondegenerate")
        h_inv = np.linalg.inv(h_i)
        k_mixed = np.einsum("ac,cb->ab", h_inv, k[index])
        k_square = np.einsum("ac,cb->ab", k[index], k_mixed)
        dk.append(r[index] + k_square)
    return {
        "partial_R_induced_metric_h_ab": dh,
        "partial_R_extrinsic_curvature_K_ab": np.asarray(dk),
    }
