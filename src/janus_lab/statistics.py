"""Small statistical utilities for model comparison."""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from typing import Callable

import numpy as np


@dataclass(frozen=True)
class FitResult:
    name: str
    chi2: float
    n_data: int
    n_params: int
    params: dict[str, float]

    @property
    def dof(self) -> int:
        return self.n_data - self.n_params

    @property
    def chi2_per_dof(self) -> float:
        return self.chi2 / self.dof if self.dof > 0 else float("nan")

    @property
    def aic(self) -> float:
        return self.chi2 + 2.0 * self.n_params

    @property
    def bic(self) -> float:
        return self.chi2 + self.n_params * np.log(self.n_data)


def chi_square(
    residuals: np.ndarray,
    covariance: np.ndarray | None = None,
    sigma: np.ndarray | None = None,
) -> float:
    """Compute chi-square from residuals and either covariance or sigma."""

    residuals = np.asarray(residuals, dtype=float)
    if covariance is not None:
        return float(residuals @ np.linalg.solve(covariance, residuals))
    if sigma is not None:
        sigma = np.asarray(sigma, dtype=float)
        return float(np.sum((residuals / sigma) ** 2))
    return float(np.sum(residuals**2))


def validate_data_vector_and_covariance(
    observed: np.ndarray,
    predicted: np.ndarray,
    covariance: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Validate a fixed-prediction Gaussian likelihood input."""

    obs = np.asarray(observed, dtype=float)
    pred = np.asarray(predicted, dtype=float)
    cov = np.asarray(covariance, dtype=float)
    if obs.ndim != 1 or pred.ndim != 1:
        raise ValueError("observed and predicted must be one-dimensional.")
    if obs.shape != pred.shape:
        raise ValueError("observed and predicted must have the same shape.")
    if cov.shape != (obs.size, obs.size):
        raise ValueError("covariance shape must match the data vector.")
    if not np.isfinite(obs).all() or not np.isfinite(pred).all() or not np.isfinite(cov).all():
        raise ValueError("likelihood inputs must be finite.")
    if not np.allclose(cov, cov.T):
        raise ValueError("covariance must be symmetric.")
    try:
        np.linalg.cholesky(cov)
    except np.linalg.LinAlgError as exc:
        raise ValueError("covariance must be positive definite.") from exc
    return obs, pred, cov


def fixed_prediction_chi_square(
    name: str,
    observed: np.ndarray,
    predicted: np.ndarray,
    covariance: np.ndarray,
    n_params: int = 0,
) -> FitResult:
    """Gaussian chi-square for a stated prediction with no hidden fitting."""

    if n_params < 0:
        raise ValueError("n_params must be non-negative.")
    obs, pred, cov = validate_data_vector_and_covariance(observed, predicted, covariance)
    return FitResult(
        name=name,
        chi2=chi_square(obs - pred, covariance=cov),
        n_data=int(obs.size),
        n_params=n_params,
        params={},
    )


def fit_additive_offset(
    observed: np.ndarray,
    predicted: np.ndarray,
    sigma: np.ndarray,
) -> float:
    """Weighted best additive offset for observed ~= predicted + offset."""

    weights = 1.0 / np.asarray(sigma, dtype=float) ** 2
    return float(np.sum(weights * (observed - predicted)) / np.sum(weights))


def grid_search(
    scorer: Callable[[dict[str, float]], float],
    grid: dict[str, Iterable[float]],
) -> tuple[dict[str, float], float]:
    """Brute-force grid search over a small parameter grid."""

    items = list(grid.items())
    best_params: dict[str, float] | None = None
    best_score = float("inf")

    def visit(index: int, current: dict[str, float]) -> None:
        nonlocal best_params, best_score
        if index == len(items):
            score = scorer(current)
            if score < best_score:
                best_score = score
                best_params = dict(current)
            return

        key, values = items[index]
        for value in values:
            current[key] = float(value)
            visit(index + 1, current)

    visit(0, {})
    if best_params is None:
        raise ValueError("Grid search received an empty grid.")
    return best_params, best_score


def weighted_linear_fit(
    design: np.ndarray,
    observed: np.ndarray,
    covariance: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, float]:
    """Generalized least squares fit for observed ~= design @ coeffs."""

    design = np.asarray(design, dtype=float)
    observed = np.asarray(observed, dtype=float)
    covariance = np.asarray(covariance, dtype=float)

    inv_cov = np.linalg.inv(covariance)
    normal = design.T @ inv_cov @ design
    rhs = design.T @ inv_cov @ observed
    try:
        coeffs = np.linalg.solve(normal, rhs)
    except np.linalg.LinAlgError:
        coeffs = np.linalg.pinv(normal) @ rhs
    prediction = design @ coeffs
    return coeffs, prediction, chi_square(observed - prediction, covariance=covariance)
