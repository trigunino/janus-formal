"""MF-MAN-013: split-conformal calibration of scale consistency in 1+1."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_poisson_minkowski2 import longest_product_chain
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_poisson_minkowski2 import longest_product_chain


PROTOCOL = {
    "protocol_id": "MF-MAN-013-v1",
    "base_seed": 2026101300,
    "physical_densities": [128, 288, 512, 800],
    "calibration_replicates": 199,
    "validation_replicates": 400,
    "alpha": 0.10,
    "calibration_rank": 180,
    "volume_region": {"lower": [0.0, 0.0], "upper": [0.5, 0.5]},
    "chain_region": {"lower": [0.5, 0.5], "upper": [1.0, 1.0]},
}


def consistency_from_points(points: np.ndarray) -> dict[str, float | int]:
    volume_points = points[(points[:, 0] < 0.5) & (points[:, 1] < 0.5)]
    chain_points = points[(points[:, 0] >= 0.5) & (points[:, 1] >= 0.5)]
    chain_steps = longest_product_chain(chain_points) + 1
    density_estimate = 8.0 * len(volume_points)  # region volume = 1/8
    chain_scale_squared = 0.25 / (chain_steps * chain_steps)
    consistency = 2.0 * density_estimate * chain_scale_squared
    return {
        "volume_count": int(len(volume_points)),
        "chain_steps": int(chain_steps),
        "density_estimate": density_estimate,
        "chain_scale_squared": chain_scale_squared,
        "two_density_chain_scale_squared": consistency,
        "absolute_distance_from_identity": abs(consistency - 1.0),
    }


def poisson_sample(density: int, seed: int) -> dict[str, float | int]:
    rng = np.random.default_rng(seed)
    points = rng.random((int(rng.poisson(density / 2)), 2))
    return consistency_from_points(points)


def square_grid(density: int) -> np.ndarray:
    side = math.isqrt(density // 2)
    if 2 * side * side != density or side % 2:
        raise ValueError("grid controls require density = 2*m^2 with even m")
    axis = (np.arange(side, dtype=float) + 0.5) / side
    return np.array([(u, v) for u in axis for v in axis], dtype=float)


def scale_conformal_audit() -> dict[str, object]:
    calibration_count = int(PROTOCOL["calibration_replicates"])
    validation_count = int(PROTOCOL["validation_replicates"])
    rank = int(PROTOCOL["calibration_rank"])
    rows = []
    for density_index, density in enumerate(PROTOCOL["physical_densities"]):
        seed_root = int(PROTOCOL["base_seed"]) + 100_000 * density_index
        calibration = [
            poisson_sample(density, seed_root + replicate)
            for replicate in range(calibration_count)
        ]
        calibration_scores = sorted(
            float(sample["absolute_distance_from_identity"])
            for sample in calibration
        )
        threshold = calibration_scores[rank - 1]
        validation = [
            poisson_sample(density, seed_root + 50_000 + replicate)
            for replicate in range(validation_count)
        ]
        validation_scores = np.array(
            [sample["absolute_distance_from_identity"] for sample in validation],
            dtype=float,
        )
        grid = consistency_from_points(square_grid(density))
        rows.append(
            {
                "physical_density": density,
                "conformal_threshold": threshold,
                "validation_coverage": float(np.mean(validation_scores <= threshold)),
                "validation_mean_consistency": float(
                    np.mean(
                        [
                            sample["two_density_chain_scale_squared"]
                            for sample in validation
                        ]
                    )
                ),
                "validation_median_score": float(np.median(validation_scores)),
                "square_grid_control": {
                    **grid,
                    "accepted": bool(grid["absolute_distance_from_identity"] <= threshold),
                },
            }
        )
    expected_rank = math.ceil(
        (calibration_count + 1) * (1 - float(PROTOCOL["alpha"]))
    )
    return {
        "program": "MF-MAN-013",
        "protocol": PROTOCOL,
        "protocol_integrity": {
            "expected_rank": expected_rank,
            "rank_matches": rank == expected_rank,
            "volume_and_chain_regions_disjoint_up_to_measure_zero": True,
            "fresh_validation_seeds": True,
        },
        "guarantee": (
            "90% marginal split-conformal coverage at each density under "
            "exchangeability; not simultaneous or conditional coverage"
        ),
        "rows": rows,
        "negative_control_gate": {
            "all_square_grids_rejected": all(
                not row["square_grid_control"]["accepted"] for row in rows
            ),
            "status": "failed_grid_collision",
        },
        "conclusion": (
            "finite Poisson fluctuations can be calibrated without choosing units, "
            "but square grids exactly collide with the identity and prove that the "
            "diagnostic is not sufficient for manifold-likeness"
        ),
        "claims_not_made": [
            "the observed validation fraction is itself a coverage proof",
            "geometric reconstruction or uniqueness",
            "physical causality, Janus structure or a throat",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(scale_conformal_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
