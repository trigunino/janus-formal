"""Strict extrinsic-curvature jump helpers for active Z2/Sigma geometry."""

from __future__ import annotations

from collections.abc import Callable

import numpy as np

from .z2_sigma_flrw_component_manifest import FORBIDDEN_PROVENANCE_TOKENS


ArrayFn = Callable[[np.ndarray], np.ndarray]
TensorFn = Callable[[float], np.ndarray]


def _checked_tensor(values, shape: tuple[int, ...], name: str) -> np.ndarray:
    tensor = np.asarray(values, dtype=float)
    if tensor.shape != shape:
        raise ValueError(f"{name} has shape {tensor.shape}, expected {shape}")
    if not np.all(np.isfinite(tensor)):
        raise ValueError(f"{name} contains non-finite values")
    return tensor


def _checked_array(values, shape: tuple[int, ...], name: str) -> np.ndarray:
    array = np.asarray(values, dtype=float)
    if array.shape != shape:
        raise ValueError(f"{name} returned shape {array.shape}, expected {shape}")
    if not np.all(np.isfinite(array)):
        raise ValueError(f"{name} returned non-finite values")
    return array


def _clean_source(source: str, field: str) -> str:
    cleaned = str(source).strip()
    if not cleaned:
        raise ValueError(f"Missing active provenance for {field}")
    lowered = cleaned.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden provenance for {field}: {cleaned}")
    return cleaned


def extrinsic_curvature_from_embedding_second_form(
    tangent_vectors: np.ndarray,
    second_embedding: np.ndarray,
    christoffel_symbols: np.ndarray,
    normal_covector: np.ndarray,
) -> np.ndarray:
    """Compute K_ab = e_a^mu e_b^nu nabla_mu n_nu from embedding data.

    Using tangency n_mu e_a^mu=0, this evaluates
    K_ab = -n_mu (partial_a partial_b X^mu + Gamma^mu_{alpha beta} e_a^alpha e_b^beta).
    All inputs are supplied by the active geometry.
    """

    tangents = np.asarray(tangent_vectors, dtype=float)
    if tangents.ndim != 2:
        raise ValueError("tangent_vectors must have shape (intrinsic_dim, ambient_dim)")
    intrinsic_dim, ambient_dim = tangents.shape
    second = _checked_tensor(
        second_embedding,
        (intrinsic_dim, intrinsic_dim, ambient_dim),
        "second_embedding",
    )
    gamma = _checked_tensor(
        christoffel_symbols,
        (ambient_dim, ambient_dim, ambient_dim),
        "christoffel_symbols",
    )
    normal = _checked_tensor(normal_covector, (ambient_dim,), "normal_covector")

    acceleration = second + np.einsum("mab,ia,jb->ijm", gamma, tangents, tangents)
    return -np.einsum("m,ijm->ij", normal, acceleration)


def reduce_flrw_extrinsic_curvature_components(
    k_ab: np.ndarray,
    spatial_inverse_metric: np.ndarray,
    *,
    tau_index: int = 0,
    spatial_indices: tuple[int, int, int] = (1, 2, 3),
) -> tuple[float, float]:
    """Reduce a Sigma extrinsic-curvature tensor to FLRW K_s and K_tau.

    K_s is the one-third spatial trace, K_s = gamma^{ij} K_ij / 3.
    K_tau is the covariant tau-tau component K_{tau tau}.
    """

    k_tensor = np.asarray(k_ab, dtype=float)
    if k_tensor.ndim != 2 or k_tensor.shape[0] != k_tensor.shape[1]:
        raise ValueError("k_ab must be a square matrix")
    dim = k_tensor.shape[0]
    if tau_index < 0 or tau_index >= dim:
        raise ValueError("tau_index is out of range")
    if len(spatial_indices) != 3 or any(index < 0 or index >= dim for index in spatial_indices):
        raise ValueError("spatial_indices must contain three valid indices")

    gamma_inv = _checked_tensor(spatial_inverse_metric, (3, 3), "spatial_inverse_metric")
    spatial_block = k_tensor[np.ix_(spatial_indices, spatial_indices)]
    k_s = float(np.einsum("ij,ij->", gamma_inv, spatial_block) / 3.0)
    k_tau = float(k_tensor[tau_index, tau_index])
    if not np.isfinite(k_s) or not np.isfinite(k_tau):
        raise ValueError("reduced extrinsic-curvature components must be finite")
    return k_s, k_tau


def build_flrw_extrinsic_curvature_component_arrays(
    a_grid,
    tangent_vectors_of_a: TensorFn,
    second_embedding_of_a: TensorFn,
    christoffel_symbols_of_a: TensorFn,
    normal_covector_of_a: TensorFn,
    spatial_inverse_metric_of_a: TensorFn,
    *,
    tau_index: int = 0,
    spatial_indices: tuple[int, int, int] = (1, 2, 3),
) -> tuple[np.ndarray, np.ndarray]:
    """Evaluate active K_s(a), K_tau(a) on a supplied positive scale-factor grid."""

    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 1:
        raise ValueError("a_grid must be one-dimensional")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")

    k_s_values: list[float] = []
    k_tau_values: list[float] = []
    for a_value in grid:
        tangents = np.asarray(tangent_vectors_of_a(float(a_value)), dtype=float)
        k_ab = extrinsic_curvature_from_embedding_second_form(
            tangents,
            second_embedding_of_a(float(a_value)),
            christoffel_symbols_of_a(float(a_value)),
            normal_covector_of_a(float(a_value)),
        )
        k_s, k_tau = reduce_flrw_extrinsic_curvature_components(
            k_ab,
            spatial_inverse_metric_of_a(float(a_value)),
            tau_index=tau_index,
            spatial_indices=spatial_indices,
        )
        k_s_values.append(k_s)
        k_tau_values.append(k_tau)
    return np.asarray(k_s_values, dtype=float), np.asarray(k_tau_values, dtype=float)


def make_z2_oriented_extrinsic_curvature_jumps(
    k_s_plus_of_a: ArrayFn,
    k_s_minus_of_a: ArrayFn,
    k_tau_plus_of_a: ArrayFn,
    k_tau_minus_of_a: ArrayFn,
    *,
    z2_orientation_sign: float,
) -> tuple[ArrayFn, ArrayFn]:
    """Return active Z2-oriented DeltaK_s(a), DeltaK_tau(a).

    The convention is DeltaK = K_plus + eps_Z2 K_minus. For the projective
    tunnel orientation eps_Z2=-1 this is the usual plus-minus jump.
    """

    if z2_orientation_sign not in (-1.0, 1.0):
        raise ValueError("z2_orientation_sign must be +1.0 or -1.0")

    eps = float(z2_orientation_sign)

    def delta_k_s(a: np.ndarray) -> np.ndarray:
        grid = np.asarray(a, dtype=float)
        if np.any(grid <= 0.0):
            raise ValueError("scale factor grid must be positive")
        k_plus = _checked_array(k_s_plus_of_a(grid), grid.shape, "k_s_plus_of_a")
        k_minus = _checked_array(k_s_minus_of_a(grid), grid.shape, "k_s_minus_of_a")
        return k_plus + eps * k_minus

    def delta_k_tau(a: np.ndarray) -> np.ndarray:
        grid = np.asarray(a, dtype=float)
        if np.any(grid <= 0.0):
            raise ValueError("scale factor grid must be positive")
        k_plus = _checked_array(k_tau_plus_of_a(grid), grid.shape, "k_tau_plus_of_a")
        k_minus = _checked_array(k_tau_minus_of_a(grid), grid.shape, "k_tau_minus_of_a")
        return k_plus + eps * k_minus

    return delta_k_s, delta_k_tau


def build_flrw_extrinsic_curvature_grid_payload(
    *,
    a_grid,
    k_s_plus,
    k_s_minus,
    k_tau_plus,
    k_tau_minus,
    z2_orientation_sign: float,
    k_provenance: str,
) -> dict:
    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    if z2_orientation_sign not in (-1.0, 1.0):
        raise ValueError("z2_orientation_sign must be +1.0 or -1.0")
    provenance = _clean_source(k_provenance, "K_provenance")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": grid.tolist(),
        "K_s_plus_Z2Sigma": _checked_array(k_s_plus, grid.shape, "k_s_plus").tolist(),
        "K_s_minus_Z2Sigma": _checked_array(k_s_minus, grid.shape, "k_s_minus").tolist(),
        "K_tau_plus_Z2Sigma": _checked_array(k_tau_plus, grid.shape, "k_tau_plus").tolist(),
        "K_tau_minus_Z2Sigma": _checked_array(k_tau_minus, grid.shape, "k_tau_minus").tolist(),
        "z2_orientation_sign": float(z2_orientation_sign),
        "K_provenance": provenance,
    }


def dynamic_spherical_shell_extrinsic_curvature_components(
    *,
    R,
    R_dot,
    R_ddot,
    f_plus,
    f_minus,
    df_plus_dR,
    df_minus_dR,
    epsilon_plus: float,
    epsilon_minus: float,
) -> dict:
    """Poisson-Visser/Lobo-Crawford dynamic spherical shell K components.

    K_s^pm = eps_pm sqrt(Rdot^2 + f_pm(R)) / R
    K_tau^pm = eps_pm (Rddot + f'_pm(R)/2) / sqrt(Rdot^2 + f_pm(R))

    Inputs are arrays on the same active shell grid. The helper is conditional:
    the bulk functions f_pm and derivatives must be derived upstream.
    """

    if epsilon_plus not in (-1.0, 1.0) or epsilon_minus not in (-1.0, 1.0):
        raise ValueError("epsilon_plus/minus must be +1.0 or -1.0")
    radius = np.asarray(R, dtype=float)
    r_dot = _checked_array(R_dot, radius.shape, "R_dot")
    r_ddot = _checked_array(R_ddot, radius.shape, "R_ddot")
    fp = _checked_array(f_plus, radius.shape, "f_plus")
    fm = _checked_array(f_minus, radius.shape, "f_minus")
    dfp = _checked_array(df_plus_dR, radius.shape, "df_plus_dR")
    dfm = _checked_array(df_minus_dR, radius.shape, "df_minus_dR")
    if np.any(radius <= 0.0):
        raise ValueError("R must be positive")
    rad_plus = r_dot * r_dot + fp
    rad_minus = r_dot * r_dot + fm
    if np.any(rad_plus <= 0.0) or np.any(rad_minus <= 0.0):
        raise ValueError("dynamic shell square-root radicands must be positive")
    sqrt_plus = np.sqrt(rad_plus)
    sqrt_minus = np.sqrt(rad_minus)
    k_s_plus = float(epsilon_plus) * sqrt_plus / radius
    k_s_minus = float(epsilon_minus) * sqrt_minus / radius
    k_tau_plus = float(epsilon_plus) * (r_ddot + 0.5 * dfp) / sqrt_plus
    k_tau_minus = float(epsilon_minus) * (r_ddot + 0.5 * dfm) / sqrt_minus
    return {
        "K_s_plus": k_s_plus,
        "K_s_minus": k_s_minus,
        "K_tau_plus": k_tau_plus,
        "K_tau_minus": k_tau_minus,
    }
