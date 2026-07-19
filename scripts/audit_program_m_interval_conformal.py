"""MF-LOC-003: fresh split-conformal calibration of interval profiles."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_blind_dimension import order_matrix_from_null_points
    from scripts.audit_program_m_interval_abundance import interval_abundance_profile
    from scripts.audit_program_m_interval_multiscale import three_layer_order
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_blind_dimension import order_matrix_from_null_points
    from audit_program_m_interval_abundance import interval_abundance_profile
    from audit_program_m_interval_multiscale import three_layer_order


PROTOCOL = {
    "protocol_id": "MF-LOC-003-v1",
    "sizes": [128, 256, 512, 1024],
    "maximum_explicit_interior_size": 20,
    "reference_replicates_per_size": 16,
    "calibration_replicates_per_size": 39,
    "validation_replicates_per_size": 40,
    "alpha": 0.10,
    "base_seed": 2026080000,
    "calibration_seed_offset": 1000,
    "validation_seed_offset": 3000,
    "three_layer_seed_offset": 5000,
    "scale_seed_stride": 10_000,
    "grid_shapes": [[8, 16], [16, 16], [16, 32], [32, 32]],
    "empirical_validation_floor": 0.80,
}


def conformal_threshold(scores: list[float], alpha: float) -> tuple[float, int]:
    """The ceil((m+1)(1-alpha))-th calibration order statistic."""
    if not scores or not 0 < alpha < 1:
        raise ValueError("scores must be nonempty and alpha must lie in (0,1)")
    rank = math.ceil((len(scores) + 1) * (1 - alpha))
    if rank > len(scores):
        return math.inf, rank
    return sorted(scores)[rank - 1], rank


def _profile(size: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    points = rng.random((size, 2))
    order = order_matrix_from_null_points(points)
    del points
    return interval_abundance_profile(
        order, int(PROTOCOL["maximum_explicit_interior_size"])
    )


def _grid_profile(shape: list[int]) -> np.ndarray:
    width, height = shape
    points = np.array([(u, v) for u in range(width) for v in range(height)])
    return interval_abundance_profile(
        order_matrix_from_null_points(points),
        int(PROTOCOL["maximum_explicit_interior_size"]),
    )


def _distance(profile: np.ndarray, centroid: np.ndarray) -> float:
    return float(np.sum(np.abs(profile - centroid)))


def _audit_size(size: int, shape: list[int], scale_index: int) -> dict[str, object]:
    base = int(PROTOCOL["base_seed"]) + scale_index * int(PROTOCOL["scale_seed_stride"])
    reference = [
        _profile(size, base + index)
        for index in range(int(PROTOCOL["reference_replicates_per_size"]))
    ]
    centroid = np.mean(np.stack(reference), axis=0)
    calibration_scores = [
        _distance(
            _profile(size, base + int(PROTOCOL["calibration_seed_offset"]) + index),
            centroid,
        )
        for index in range(int(PROTOCOL["calibration_replicates_per_size"]))
    ]
    threshold, rank = conformal_threshold(calibration_scores, float(PROTOCOL["alpha"]))
    validation_scores = [
        _distance(
            _profile(size, base + int(PROTOCOL["validation_seed_offset"]) + index),
            centroid,
        )
        for index in range(int(PROTOCOL["validation_replicates_per_size"]))
    ]
    empirical_coverage = sum(score <= threshold for score in validation_scores) / len(
        validation_scores
    )
    grid_distance = _distance(_grid_profile(shape), centroid)
    layered = three_layer_order(size, base + int(PROTOCOL["three_layer_seed_offset"]))
    layered_distance = _distance(
        interval_abundance_profile(
            layered, int(PROTOCOL["maximum_explicit_interior_size"])
        ),
        centroid,
    )
    calibration_size = len(calibration_scores)
    return {
        "elements": size,
        "reference_centroid": centroid.tolist(),
        "conformal_rank": rank,
        "calibration_size": calibration_size,
        "finite_marginal_coverage_lower_bound": rank / (calibration_size + 1),
        "frozen_threshold": threshold,
        "empirical_validation_coverage": empirical_coverage,
        "empirical_validation_floor_pass": (
            empirical_coverage >= float(PROTOCOL["empirical_validation_floor"])
        ),
        "grid_distance": grid_distance,
        "grid_rejected": grid_distance > threshold,
        "three_layer_distance": layered_distance,
        "three_layer_rejected": layered_distance > threshold,
    }


def run_audit() -> dict[str, object]:
    rows = [
        _audit_size(size, shape, index)
        for index, (size, shape) in enumerate(
            zip(PROTOCOL["sizes"], PROTOCOL["grid_shapes"], strict=True)
        )
    ]
    gates = {
        "finite_coverage_bound_is_90_percent_all_scales": all(
            row["finite_marginal_coverage_lower_bound"] >= 0.90 for row in rows
        ),
        "empirical_validation_floor_all_scales": all(
            row["empirical_validation_floor_pass"] for row in rows
        ),
        "grids_rejected_all_scales": all(row["grid_rejected"] for row in rows),
        "three_layer_rejected_all_scales": all(
            row["three_layer_rejected"] for row in rows
        ),
    }
    gates["all_preregistered_gates"] = all(gates.values())
    return {
        "program": "MF-LOC-003",
        "protocol": PROTOCOL,
        "numpy_version": np.__version__,
        "results": rows,
        "gates": gates,
        "guarantee_scope": (
            "90% marginal coverage per scale under exchangeability; not simultaneous, "
            "conditional, or manifold-likeness coverage"
        ),
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
