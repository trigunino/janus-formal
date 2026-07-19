"""MF-LOC-002: multiscale interval profiles with grid and three-layer controls."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_blind_dimension import order_matrix_from_null_points
    from scripts.audit_program_m_interval_abundance import interval_abundance_profile
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_blind_dimension import order_matrix_from_null_points
    from audit_program_m_interval_abundance import interval_abundance_profile


PROTOCOL = {
    "protocol_id": "MF-LOC-002-v1",
    "sizes": [128, 256, 512, 1024],
    "maximum_explicit_interior_size": 20,
    "training_replicates_per_size": 16,
    "validation_replicates_per_size": 16,
    "base_seed": 2026074000,
    "validation_seed_offset": 5000,
    "three_layer_seed_offset": 9000,
    "threshold_rule": "per size: 1.25 times maximum training L1 distance",
    "validation_acceptance_min": 0.90,
    "grid_shapes": [[8, 16], [16, 16], [16, 32], [32, 32]],
    "three_layer_fractions": [0.25, 0.50, 0.25],
    "adjacent_layer_edge_probability": 0.50,
}


def three_layer_order(size: int, seed: int) -> np.ndarray:
    """KR-type three-layer order with explicit transitive bottom-top closure."""
    if size % 4:
        raise ValueError("three-layer control size must be divisible by four")
    bottom_size = size // 4
    middle_size = size // 2
    top_size = size // 4
    rng = np.random.default_rng(seed)
    bottom_middle = rng.random((bottom_size, middle_size)) < 0.5
    middle_top = rng.random((middle_size, top_size)) < 0.5
    bottom_top = (bottom_middle.astype(np.uint16) @ middle_top.astype(np.uint16)) > 0
    order = np.eye(size, dtype=bool)
    bottom = slice(0, bottom_size)
    middle = slice(bottom_size, bottom_size + middle_size)
    top = slice(bottom_size + middle_size, size)
    order[bottom, middle] = bottom_middle
    order[middle, top] = middle_top
    order[bottom, top] = bottom_top
    return order


def is_transitive(order: np.ndarray) -> bool:
    reach_two = (order.astype(np.uint16) @ order.astype(np.uint16)) > 0
    return bool(np.all(~reach_two | order))


def _poisson_profile(size: int, seed: int) -> np.ndarray:
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


def _l1(first: np.ndarray, second: np.ndarray) -> float:
    return float(np.sum(np.abs(first - second)))


def _audit_size(size: int, shape: list[int], scale_index: int) -> dict[str, object]:
    seed_base = int(PROTOCOL["base_seed"]) + 10_000 * scale_index
    training = [
        _poisson_profile(size, seed_base + index)
        for index in range(int(PROTOCOL["training_replicates_per_size"]))
    ]
    centroid = np.mean(np.stack(training), axis=0)
    training_distances = [_l1(profile, centroid) for profile in training]
    threshold = 1.25 * max(training_distances)
    validation = [
        _poisson_profile(
            size,
            seed_base + int(PROTOCOL["validation_seed_offset"]) + index,
        )
        for index in range(int(PROTOCOL["validation_replicates_per_size"]))
    ]
    validation_distances = [_l1(profile, centroid) for profile in validation]
    acceptance = sum(distance <= threshold for distance in validation_distances) / len(
        validation_distances
    )
    grid_distance = _l1(_grid_profile(shape), centroid)
    layered = three_layer_order(
        size, seed_base + int(PROTOCOL["three_layer_seed_offset"])
    )
    layered_distance = _l1(
        interval_abundance_profile(
            layered, int(PROTOCOL["maximum_explicit_interior_size"])
        ),
        centroid,
    )
    return {
        "elements": size,
        "grid_shape": shape,
        "frozen_threshold": threshold,
        "validation_acceptance": acceptance,
        "validation_gate": acceptance >= float(PROTOCOL["validation_acceptance_min"]),
        "grid_distance": grid_distance,
        "grid_rejected": grid_distance > threshold,
        "three_layer_distance": layered_distance,
        "three_layer_rejected": layered_distance > threshold,
        "three_layer_transitive": is_transitive(layered),
    }


def run_audit() -> dict[str, object]:
    rows = [
        _audit_size(size, shape, index)
        for index, (size, shape) in enumerate(
            zip(PROTOCOL["sizes"], PROTOCOL["grid_shapes"], strict=True)
        )
    ]
    poisson_gate = all(row["validation_gate"] for row in rows)
    grid_gate = all(row["grid_rejected"] for row in rows)
    layered_gate = all(row["three_layer_rejected"] for row in rows)
    transitivity_gate = all(row["three_layer_transitive"] for row in rows)
    return {
        "program": "MF-LOC-002",
        "protocol": PROTOCOL,
        "numpy_version": np.__version__,
        "results": rows,
        "gates": {
            "poisson_validation_all_scales": poisson_gate,
            "grids_rejected_all_scales": grid_gate,
            "three_layer_rejected_all_scales": layered_gate,
            "three_layer_orders_all_transitive": transitivity_gate,
            "all_preregistered_gates": (
                poisson_gate and grid_gate and layered_gate and transitivity_gate
            ),
        },
        "scope": "finite scale-specific calibration; not a universal locality theorem",
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
