"""MF-LOC-001: coordinate-blind interval-abundance locality audit."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_blind_dimension import order_matrix_from_null_points
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_blind_dimension import order_matrix_from_null_points


PROTOCOL = {
    "protocol_id": "MF-LOC-001-v1",
    "elements": 512,
    "maximum_explicit_interior_size": 20,
    "training_base_seed": 2026072000,
    "training_replicates": 32,
    "validation_base_seed": 2026073000,
    "validation_replicates": 32,
    "threshold_rule": "1.25 times maximum training L1 distance to training centroid",
    "validation_acceptance_min": 0.90,
    "negative_control": "regular 16x32 product grid",
}


def _bit_rows(matrix: np.ndarray) -> list[int]:
    return [
        sum(1 << int(index) for index in np.flatnonzero(row))
        for row in matrix
    ]


def interval_abundance_profile(order: np.ndarray, maximum_interior: int) -> np.ndarray:
    """Normalized strict-interval histogram from an order matrix only.

    Bins `0..maximum_interior` are exact; the final bin is overflow.
    """
    matrix = np.asarray(order, dtype=bool)
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError("order must be a square matrix")
    if maximum_interior < 0:
        raise ValueError("maximum_interior must be nonnegative")
    strict = matrix.copy()
    np.fill_diagonal(strict, False)
    future = _bit_rows(matrix)
    past = _bit_rows(matrix.T)
    histogram = np.zeros(maximum_interior + 2, dtype=float)
    for lower in range(matrix.shape[0]):
        for upper in np.flatnonzero(strict[lower]):
            interior = (future[lower] & past[int(upper)]).bit_count() - 2
            histogram[min(interior, maximum_interior + 1)] += 1
    total = float(np.sum(histogram))
    return histogram / total if total else histogram


def _poisson_profile(seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    points = rng.random((int(PROTOCOL["elements"]), 2))
    order = order_matrix_from_null_points(points)
    del points
    return interval_abundance_profile(
        order, int(PROTOCOL["maximum_explicit_interior_size"])
    )


def _grid_profile() -> np.ndarray:
    points = np.array([(u, v) for u in range(16) for v in range(32)], dtype=float)
    order = order_matrix_from_null_points(points)
    return interval_abundance_profile(
        order, int(PROTOCOL["maximum_explicit_interior_size"])
    )


def _l1(first: np.ndarray, second: np.ndarray) -> float:
    return float(np.sum(np.abs(first - second)))


def run_audit() -> dict[str, object]:
    training = [
        _poisson_profile(int(PROTOCOL["training_base_seed"]) + index)
        for index in range(int(PROTOCOL["training_replicates"]))
    ]
    centroid = np.mean(np.stack(training), axis=0)
    training_distances = [_l1(profile, centroid) for profile in training]
    threshold = 1.25 * max(training_distances)
    validation = [
        _poisson_profile(int(PROTOCOL["validation_base_seed"]) + index)
        for index in range(int(PROTOCOL["validation_replicates"]))
    ]
    validation_distances = [_l1(profile, centroid) for profile in validation]
    acceptance = sum(distance <= threshold for distance in validation_distances) / len(
        validation_distances
    )
    grid_profile = _grid_profile()
    grid_distance = _l1(grid_profile, centroid)
    validation_gate = acceptance >= float(PROTOCOL["validation_acceptance_min"])
    grid_rejected = grid_distance > threshold
    return {
        "program": "MF-LOC-001",
        "protocol": PROTOCOL,
        "numpy_version": np.__version__,
        "calibration": {
            "centroid": centroid.tolist(),
            "training_distances": training_distances,
            "frozen_threshold": threshold,
        },
        "held_out_validation": {
            "distances": validation_distances,
            "acceptance_fraction": acceptance,
            "gate": validation_gate,
        },
        "negative_control": {
            "profile": grid_profile.tolist(),
            "distance": grid_distance,
            "rejected": grid_rejected,
        },
        "gates": {
            "held_out_poisson_accepted": validation_gate,
            "anisotropic_grid_rejected": grid_rejected,
            "all": validation_gate and grid_rejected,
        },
        "scope": "order-only necessary locality diagnostic; not manifold-likeness",
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
