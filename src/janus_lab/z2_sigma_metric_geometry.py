"""Metric geometry primitives for the active Z2/Sigma tunnel path."""

from __future__ import annotations

import numpy as np


def _checked_tensor(values, shape: tuple[int, ...], name: str) -> np.ndarray:
    tensor = np.asarray(values, dtype=float)
    if tensor.shape != shape:
        raise ValueError(f"{name} has shape {tensor.shape}, expected {shape}")
    if not np.all(np.isfinite(tensor)):
        raise ValueError(f"{name} contains non-finite values")
    return tensor


def inverse_metric(metric_covariant: np.ndarray) -> np.ndarray:
    """Invert a nondegenerate covariant metric supplied by the active geometry."""

    metric = np.asarray(metric_covariant, dtype=float)
    if metric.ndim != 2 or metric.shape[0] != metric.shape[1]:
        raise ValueError("metric_covariant must be a square matrix")
    if not np.allclose(metric, metric.T):
        raise ValueError("metric_covariant must be symmetric")
    if not np.all(np.isfinite(metric)):
        raise ValueError("metric_covariant contains non-finite values")
    return np.linalg.inv(metric)


def christoffel_symbols_from_metric_derivatives(
    metric_inverse: np.ndarray,
    metric_derivatives: np.ndarray,
) -> np.ndarray:
    """Compute Levi-Civita Gamma^mu_{alpha beta}.

    `metric_derivatives[a,b,c]` is partial_a g_{bc}.
    """

    inv = np.asarray(metric_inverse, dtype=float)
    if inv.ndim != 2 or inv.shape[0] != inv.shape[1]:
        raise ValueError("metric_inverse must be a square matrix")
    dim = inv.shape[0]
    dg = _checked_tensor(metric_derivatives, (dim, dim, dim), "metric_derivatives")
    gamma = 0.5 * np.einsum("mn,abn->mab", inv, dg + np.swapaxes(dg, 0, 1) - np.moveaxis(dg, 0, 2))
    return gamma


def normalize_level_set_normal_covector(
    level_gradient_covector: np.ndarray,
    metric_inverse: np.ndarray,
    *,
    normal_norm_sign: float,
    orientation_sign: float = 1.0,
) -> np.ndarray:
    """Normalize a hypersurface normal covector from an active level-set gradient."""

    if normal_norm_sign not in (-1.0, 1.0):
        raise ValueError("normal_norm_sign must be +1.0 or -1.0")
    if orientation_sign not in (-1.0, 1.0):
        raise ValueError("orientation_sign must be +1.0 or -1.0")
    grad = np.asarray(level_gradient_covector, dtype=float)
    if grad.ndim != 1 or not np.all(np.isfinite(grad)):
        raise ValueError("level_gradient_covector must be a finite vector")
    inv = _checked_tensor(metric_inverse, (grad.shape[0], grad.shape[0]), "metric_inverse")
    raw_norm = float(np.einsum("m,mn,n->", grad, inv, grad))
    if raw_norm == 0.0 or not np.isfinite(raw_norm):
        raise ValueError("level-set normal must be non-null and finite")
    if np.sign(raw_norm) != normal_norm_sign:
        raise ValueError("level-set normal sign does not match normal_norm_sign")
    return float(orientation_sign) * grad / np.sqrt(abs(raw_norm))


def induced_metric_from_tangents(metric_covariant: np.ndarray, tangent_vectors: np.ndarray) -> np.ndarray:
    """Pull back the ambient metric to Sigma: h_ab = g_mn e_a^m e_b^n."""

    metric = np.asarray(metric_covariant, dtype=float)
    tangents = np.asarray(tangent_vectors, dtype=float)
    if metric.ndim != 2 or metric.shape[0] != metric.shape[1]:
        raise ValueError("metric_covariant must be a square matrix")
    if tangents.ndim != 2 or tangents.shape[1] != metric.shape[0]:
        raise ValueError("tangent_vectors must have shape (intrinsic_dim, ambient_dim)")
    if not np.all(np.isfinite(metric)) or not np.all(np.isfinite(tangents)):
        raise ValueError("metric and tangent vectors must be finite")
    return np.einsum("mn,am,bn->ab", metric, tangents, tangents)
