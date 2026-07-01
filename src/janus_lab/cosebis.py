"""COSEBIs filter/operator utilities.

This implements the survey-side log-COSEBIs transform from shear correlation
functions to E-mode coefficients. It does not generate a physical Janus
``xi_+``/``xi_-`` prediction by itself.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class LogCosebisFilter:
    mode: int
    theta_min: float
    theta_max: float
    tplus_coefficients: np.ndarray


def _legendre_grid(theta_min: float, theta_max: float, samples: int) -> tuple[np.ndarray, np.ndarray]:
    if theta_min <= 0.0 or theta_max <= theta_min:
        raise ValueError("theta range must satisfy 0 < theta_min < theta_max.")
    if samples < 64:
        raise ValueError("samples must be at least 64.")
    x, w = np.polynomial.legendre.leggauss(samples)
    log_max = float(np.log(theta_max / theta_min))
    z = 0.5 * log_max * (x + 1.0)
    weights = 0.5 * log_max * w
    return z, weights


def _poly_values(coefficients: np.ndarray, z: np.ndarray) -> np.ndarray:
    coeffs = np.asarray(coefficients, dtype=float)
    powers = np.vstack([z**index for index in range(coeffs.size)])
    return coeffs @ powers


def _moment_vector(max_degree: int, exponent: float, z: np.ndarray, weights: np.ndarray) -> np.ndarray:
    exp_weight = np.exp(exponent * z) * weights
    return np.asarray(
        [float(np.sum(exp_weight * z**degree)) for degree in range(max_degree + 1)],
        dtype=float,
    )


def _constraint_matrix(max_degree: int, z: np.ndarray, weights: np.ndarray) -> np.ndarray:
    return np.vstack(
        [
            _moment_vector(max_degree, 2.0, z, weights),
            _moment_vector(max_degree, 4.0, z, weights),
        ]
    )


def _weighted_inner(
    left: np.ndarray,
    right: np.ndarray,
    z: np.ndarray,
    weights: np.ndarray,
) -> float:
    return float(np.sum(weights * np.exp(2.0 * z) * _poly_values(left, z) * _poly_values(right, z)))


def _pad(coefficients: np.ndarray, length: int) -> np.ndarray:
    result = np.zeros(length, dtype=float)
    result[: coefficients.size] = coefficients
    return result


def log_cosebis_filters(
    n_max: int,
    theta_min: float = 0.5,
    theta_max: float = 300.0,
    *,
    samples: int = 1024,
) -> list[LogCosebisFilter]:
    """Build orthonormal log-COSEBIs ``T_+`` polynomial filters.

    The polynomial basis is ``z=ln(theta/theta_min)``. The two finite-interval
    E/B separation constraints are enforced numerically, then the remaining
    space is orthonormalized with weight ``theta dtheta``.
    """

    if n_max <= 0:
        raise ValueError("n_max must be positive.")
    z, weights = _legendre_grid(theta_min, theta_max, samples)
    filters: list[LogCosebisFilter] = []
    for mode in range(1, n_max + 1):
        degree = mode + 1
        constraints = _constraint_matrix(degree, z, weights)
        _, _, vh = np.linalg.svd(constraints)
        nullspace = vh[2:].T
        target = np.zeros(degree + 1, dtype=float)
        target[-1] = 1.0
        candidate = nullspace @ (nullspace.T @ target)
        for previous in filters:
            previous_coeffs = _pad(previous.tplus_coefficients, degree + 1)
            projection = theta_min**2 * _weighted_inner(candidate, previous_coeffs, z, weights)
            candidate = candidate - projection * previous_coeffs
        norm = np.sqrt(theta_min**2 * _weighted_inner(candidate, candidate, z, weights))
        if not np.isfinite(norm) or norm <= 0.0:
            raise ValueError(f"could not construct COSEBIs mode {mode}.")
        filters.append(
            LogCosebisFilter(
                mode=mode,
                theta_min=theta_min,
                theta_max=theta_max,
                tplus_coefficients=candidate / norm,
            )
        )
    return filters


def evaluate_tplus(filter_: LogCosebisFilter, theta: np.ndarray) -> np.ndarray:
    theta_values = np.asarray(theta, dtype=float)
    if np.any(theta_values <= 0.0):
        raise ValueError("theta values must be positive.")
    z = np.log(theta_values / filter_.theta_min)
    values = _poly_values(filter_.tplus_coefficients, z)
    return np.where(
        (theta_values >= filter_.theta_min) & (theta_values <= filter_.theta_max),
        values,
        0.0,
    )


def evaluate_tminus(filter_: LogCosebisFilter, theta: np.ndarray) -> np.ndarray:
    """Evaluate ``T_-`` from ``T_+`` on an ascending theta grid."""

    theta_values = np.asarray(theta, dtype=float)
    if theta_values.ndim != 1 or np.any(np.diff(theta_values) <= 0.0):
        raise ValueError("theta must be a strictly increasing one-dimensional grid.")
    tplus = evaluate_tplus(filter_, theta_values)
    result = np.empty_like(theta_values)
    for index, theta_i in enumerate(theta_values):
        upper_theta = theta_values[index:]
        upper_tplus = tplus[index:]
        integrand = upper_tplus / upper_theta * (1.0 - 3.0 * theta_i**2 / upper_theta**2)
        result[index] = tplus[index] + 4.0 * float(np.trapezoid(integrand, upper_theta))
    return result


def cosebis_en_from_xi(
    theta: np.ndarray,
    xi_plus: np.ndarray,
    xi_minus: np.ndarray,
    filter_: LogCosebisFilter,
) -> float:
    """Apply one COSEBIs filter to shear correlation functions."""

    theta_values = np.asarray(theta, dtype=float)
    plus = np.asarray(xi_plus, dtype=float)
    minus = np.asarray(xi_minus, dtype=float)
    if theta_values.ndim != 1 or plus.shape != theta_values.shape or minus.shape != theta_values.shape:
        raise ValueError("theta, xi_plus and xi_minus must be matching one-dimensional arrays.")
    if np.any(np.diff(theta_values) <= 0.0):
        raise ValueError("theta must be strictly increasing.")
    mask = (theta_values >= filter_.theta_min) & (theta_values <= filter_.theta_max)
    if np.count_nonzero(mask) < 8:
        raise ValueError("theta grid has too few points inside the COSEBIs support.")
    support_theta = theta_values[mask]
    tplus = evaluate_tplus(filter_, support_theta)
    tminus = evaluate_tminus(filter_, support_theta)
    integrand = support_theta * (tplus * plus[mask] + tminus * minus[mask])
    return 0.5 * float(np.trapezoid(integrand, support_theta))


def cosebis_vector_from_xi(
    theta: np.ndarray,
    xi_plus_by_pair: dict[tuple[int, int], np.ndarray],
    xi_minus_by_pair: dict[tuple[int, int], np.ndarray],
    en_rows: list[dict],
    *,
    theta_min: float = 0.5,
    theta_max: float = 300.0,
    n_max: int | None = None,
) -> list[float]:
    """Return COSEBIs values in the same row order as a KiDS ``En`` table."""

    max_mode = n_max or max(int(row["ANGBIN"]) for row in en_rows)
    filters = {item.mode: item for item in log_cosebis_filters(max_mode, theta_min, theta_max)}
    vector = []
    for row in en_rows:
        pair = (int(row["BIN1"]), int(row["BIN2"]))
        mode = int(row["ANGBIN"])
        vector.append(cosebis_en_from_xi(theta, xi_plus_by_pair[pair], xi_minus_by_pair[pair], filters[mode]))
    return vector
