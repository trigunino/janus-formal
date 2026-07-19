"""MF-MAN-015: coordinate-free immediate-link fluctuation gate."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_blind_dimension import order_matrix_from_null_points
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_blind_dimension import order_matrix_from_null_points


PROTOCOL = {
    "protocol_id": "MF-MAN-015-v1",
    "base_seed": 2026101700,
    "cardinalities": [144, 256, 576, 784],
    "calibration_replicates": 79,
    "validation_replicates": 80,
    "alpha": 0.10,
    "lower_rank": 4,
    "upper_rank": 76,
}


def _fano(values: np.ndarray) -> float:
    mean = float(np.mean(values))
    return float(np.var(values, ddof=1) / mean) if mean > 0 else 0.0


def immediate_link_degrees(order: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    matrix = np.asarray(order, dtype=bool)
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError("order must be a square matrix")
    size = matrix.shape[0]
    future_bits = [
        sum(1 << int(target) for target in np.flatnonzero(matrix[source]))
        for source in range(size)
    ]
    past_bits = [
        sum(1 << int(source) for source in np.flatnonzero(matrix[:, target]))
        for target in range(size)
    ]
    out_degree = np.zeros(size, dtype=int)
    in_degree = np.zeros(size, dtype=int)
    for source in range(size):
        for raw_target in np.flatnonzero(matrix[source]):
            target = int(raw_target)
            if source == target:
                continue
            interval_size = (future_bits[source] & past_bits[target]).bit_count()
            if interval_size == 2:
                out_degree[source] += 1
                in_degree[target] += 1
    return out_degree, in_degree


def intrinsic_link_fluctuation(order: np.ndarray) -> float:
    """Orientation-symmetric dispersion of immediate-link degrees."""
    out_degree, in_degree = immediate_link_degrees(order)
    return (_fano(out_degree) + _fano(in_degree)) / 2


def conditioned_poisson_order(cardinality: int, seed: int) -> np.ndarray:
    points = np.random.default_rng(seed).random((cardinality, 2))
    order = order_matrix_from_null_points(points)
    del points
    return order


def square_grid_order(cardinality: int) -> np.ndarray:
    side = math.isqrt(cardinality)
    if side * side != cardinality:
        raise ValueError("square-grid control requires a square cardinality")
    axis = (np.arange(side, dtype=float) + 0.5) / side
    points = np.array([(u, v) for u in axis for v in axis], dtype=float)
    order = order_matrix_from_null_points(points)
    del points
    return order


def chain_order(cardinality: int) -> np.ndarray:
    return np.triu(np.ones((cardinality, cardinality), dtype=bool))


def intrinsic_link_fluctuation_audit() -> dict[str, object]:
    calibration_count = int(PROTOCOL["calibration_replicates"])
    validation_count = int(PROTOCOL["validation_replicates"])
    lower_rank = int(PROTOCOL["lower_rank"])
    upper_rank = int(PROTOCOL["upper_rank"])
    rows = []
    for size_index, cardinality in enumerate(PROTOCOL["cardinalities"]):
        seed_root = int(PROTOCOL["base_seed"]) + 100_000 * size_index
        calibration = sorted(
            intrinsic_link_fluctuation(
                conditioned_poisson_order(cardinality, seed_root + replicate)
            )
            for replicate in range(calibration_count)
        )
        lower = calibration[lower_rank - 1]
        upper = calibration[upper_rank - 1]
        validation = np.array(
            [
                intrinsic_link_fluctuation(
                    conditioned_poisson_order(
                        cardinality, seed_root + 50_000 + replicate
                    )
                )
                for replicate in range(validation_count)
            ]
        )
        grid_score = intrinsic_link_fluctuation(square_grid_order(cardinality))
        chain_score = intrinsic_link_fluctuation(chain_order(cardinality))
        rows.append(
            {
                "cardinality": cardinality,
                "acceptance_interval": [lower, upper],
                "validation_coverage": float(
                    np.mean((lower <= validation) & (validation <= upper))
                ),
                "square_grid_control": {
                    "score": grid_score,
                    "accepted": lower <= grid_score <= upper,
                },
                "chain_control": {
                    "score": chain_score,
                    "accepted": lower <= chain_score <= upper,
                },
            }
        )
    return {
        "program": "MF-MAN-015",
        "input": "finite partial-order matrix only",
        "statistic": (
            "mean of the in-link and out-link degree Fano factors; a link is an "
            "ordered pair whose closed interval has exactly two elements"
        ),
        "protocol": PROTOCOL,
        "guarantee": (
            "90% marginal two-sided split-conformal coverage per cardinality "
            "under exchangeability; not simultaneous or conditional coverage"
        ),
        "invariances": {
            "object_relabelling": "exact by construction",
            "orientation_reversal": "exact because in/out Fano factors are averaged",
            "coordinates_used_by_statistic": False,
        },
        "rows": rows,
        "negative_control_gate": {
            "all_square_grids_rejected": all(
                not row["square_grid_control"]["accepted"] for row in rows
            ),
            "all_chains_rejected": all(
                not row["chain_control"]["accepted"] for row in rows
            ),
        },
        "retained_failed_pilot": (
            "the Fano factor of total future-set sizes was rejected because square "
            "grids overlap the Poisson reference range"
        ),
        "claims_not_made": [
            "sufficiency for manifold-likeness",
            "Lorentzian dimension or metric reconstruction",
            "physical interpretation of the mathematical orientation",
            "Janus structure or a throat",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(
        intrinsic_link_fluctuation_audit(), indent=2, sort_keys=True
    ) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
