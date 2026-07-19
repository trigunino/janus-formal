"""MF-DIM-001: coordinate-blind Myrheim--Meyer dimension audit."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np


PROTOCOL = {
    "protocol_id": "MF-DIM-001-v1",
    "validation_base_seed": 20260719,
    "validation_replicates": 64,
    "validation_density": 1024,
    "thresholds": {
        "ensemble_mean_abs_error_max": 0.10,
        "individual_interval": [1.70, 2.30],
        "individual_coverage_min": 0.90,
    },
}


def theoretical_ordering_fraction(dimension: float) -> float:
    """Large-density Minkowski ordering fraction r(d)."""
    if dimension <= 0:
        raise ValueError("dimension must be positive")
    log_value = (
        math.lgamma(dimension + 1)
        + math.lgamma(dimension / 2)
        - math.log(2)
        - math.lgamma(3 * dimension / 2)
    )
    return math.exp(log_value)


def ordering_fraction(order: np.ndarray) -> float | None:
    """Order-only invariant; coordinates are neither accepted nor inspected."""
    matrix = np.asarray(order, dtype=bool)
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError("order must be a square matrix")
    size = matrix.shape[0]
    if size < 2:
        return None
    strict = matrix.copy()
    np.fill_diagonal(strict, False)
    relations = int(np.count_nonzero(strict))
    return 2 * relations / (size * (size - 1))


def myrheim_meyer_dimension(order: np.ndarray, maximum_dimension: float = 20.0) -> float:
    """Invert r(d) by bisection using only the supplied order matrix."""
    fraction = ordering_fraction(order)
    if fraction is None:
        return math.nan
    if fraction <= theoretical_ordering_fraction(maximum_dimension):
        return math.inf
    if fraction >= 1.0 - 1e-14:
        return 1.0
    lower, upper = 1.0, maximum_dimension
    for _ in range(80):
        middle = (lower + upper) / 2
        if theoretical_ordering_fraction(middle) > fraction:
            lower = middle
        else:
            upper = middle
    return (lower + upper) / 2


def order_matrix_from_null_points(points: np.ndarray) -> np.ndarray:
    """Generator-side helper. The estimator itself never receives coordinates."""
    u = points[:, 0]
    v = points[:, 1]
    return (u[:, None] <= u[None, :]) & (v[:, None] <= v[None, :])


def _held_out_dimension(seed: int, density: int) -> dict[str, float | int]:
    rng = np.random.default_rng(seed)
    count = int(rng.poisson(density / 2))
    points = rng.random((count, 2))
    order = order_matrix_from_null_points(points)
    del points
    return {
        "elements": count,
        "ordering_fraction": float(ordering_fraction(order)),
        "estimated_dimension": myrheim_meyer_dimension(order),
    }


def _chain_order(size: int) -> np.ndarray:
    indices = np.arange(size)
    return indices[:, None] <= indices[None, :]


def _antichain_order(size: int) -> np.ndarray:
    return np.eye(size, dtype=bool)


def _grid_order(linear_size: int) -> np.ndarray:
    points = np.array(
        [(u, v) for u in range(linear_size) for v in range(linear_size)],
        dtype=float,
    )
    return order_matrix_from_null_points(points)


def run_audit() -> dict[str, object]:
    density = int(PROTOCOL["validation_density"])
    samples = [
        _held_out_dimension(int(PROTOCOL["validation_base_seed"]) + index, density)
        for index in range(int(PROTOCOL["validation_replicates"]))
    ]
    estimates = np.array([sample["estimated_dimension"] for sample in samples])
    lower, upper = PROTOCOL["thresholds"]["individual_interval"]
    mean_estimate = float(np.mean(estimates))
    coverage = float(np.mean((lower <= estimates) & (estimates <= upper)))
    validation_pass = (
        abs(mean_estimate - 2) <= PROTOCOL["thresholds"]["ensemble_mean_abs_error_max"]
        and coverage >= PROTOCOL["thresholds"]["individual_coverage_min"]
    )
    chain = _chain_order(128)
    antichain = _antichain_order(128)
    grid = _grid_order(24)
    return {
        "program": "MF-DIM-001",
        "protocol": PROTOCOL,
        "numpy_version": np.__version__,
        "analytic_reference": {
            "r_of_1": theoretical_ordering_fraction(1),
            "r_of_2": theoretical_ordering_fraction(2),
            "r_of_3": theoretical_ordering_fraction(3),
            "r_of_4": theoretical_ordering_fraction(4),
        },
        "held_out_validation": {
            "ensemble_mean_estimated_dimension": mean_estimate,
            "ensemble_standard_deviation": float(np.std(estimates, ddof=1)),
            "individual_interval_coverage": coverage,
            "gate": validation_pass,
            "samples": samples,
        },
        "controls": {
            "total_chain_estimate": myrheim_meyer_dimension(chain),
            "antichain_estimate": "infinity"
            if math.isinf(myrheim_meyer_dimension(antichain))
            else myrheim_meyer_dimension(antichain),
            "anisotropic_grid_24x24": {
                "ordering_fraction": ordering_fraction(grid),
                "estimated_dimension": myrheim_meyer_dimension(grid),
                "known_failure": "MF-MAN-006 directional chain-time anisotropy",
            },
        },
        "conclusion": "necessary order-only diagnostic, not manifold-likeness",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(run_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
