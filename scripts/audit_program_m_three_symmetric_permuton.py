"""MF-ADV-009: a non-uniform 3-symmetric permuton adversary."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_pattern_ladder import (
        exact_minkowski_distribution,
        sampled_distribution,
        total_variation,
    )
    from scripts.audit_program_m_ensemble_separation import minkowski_order
except ModuleNotFoundError:
    from audit_program_m_pattern_ladder import (
        exact_minkowski_distribution,
        sampled_distribution,
        total_variation,
    )
    from audit_program_m_ensemble_separation import minkowski_order


# Khovanova--Zhang, arXiv:1809.08490. The earlier claimed size-9
# construction repeated in arXiv:1205.3074 is incorrect.
INFLATABLE_PERMUTATION = np.array(
    [13, 4, 2, 3, 10, 15, 9, 8, 16, 11, 1, 12, 0, 5, 7, 6, 14]
)
PROTOCOL = {
    "protocol_id": "MF-ADV-009-v1",
    "base_seed": 2026071811,
    "ranks": [2, 3, 4],
    "samples_per_batch": 8192,
    "calibration_batches": 99,
    "validation_batches": 32,
    "upper_rank": 99,
    "source": "Khovanova--Zhang arXiv:1809.08490",
}


def three_symmetric_permuton_order(size: int, rng: np.random.Generator) -> np.ndarray:
    """Sample iid points from the 9-cell permuton and take product order."""
    cells = rng.integers(0, len(INFLATABLE_PERMUTATION), size=size)
    x = (cells + rng.random(size)) / len(INFLATABLE_PERMUTATION)
    y = (INFLATABLE_PERMUTATION[cells] + rng.random(size)) / len(
        INFLATABLE_PERMUTATION
    )
    points = np.column_stack((x, y))
    return np.all(points[:, None, :] <= points[None, :, :], axis=2)


def run_audit() -> dict[str, object]:
    rows = []
    for rank in PROTOCOL["ranks"]:
        reference = exact_minkowski_distribution(rank)
        calibration = sorted(
            total_variation(
                sampled_distribution(
                    minkowski_order,
                    rank,
                    int(PROTOCOL["samples_per_batch"]),
                    int(PROTOCOL["base_seed"]) + 100_000 * rank + batch,
                ),
                reference,
            )
            for batch in range(int(PROTOCOL["calibration_batches"]))
        )
        threshold = calibration[int(PROTOCOL["upper_rank"]) - 1]
        distances = [
            total_variation(
                sampled_distribution(
                    three_symmetric_permuton_order,
                    rank,
                    int(PROTOCOL["samples_per_batch"]),
                    int(PROTOCOL["base_seed"])
                    + 10_000_000
                    + 100_000 * rank
                    + batch,
                ),
                reference,
            )
            for batch in range(int(PROTOCOL["validation_batches"]))
        ]
        rows.append(
            {
                "rank": rank,
                "threshold_total_variation": threshold,
                "mean_total_variation": float(np.mean(distances)),
                "acceptance_rate": float(np.mean(np.array(distances) <= threshold)),
            }
        )
    by_rank = {row["rank"]: row for row in rows}
    return {
        "program": "MF-ADV-009",
        "protocol": PROTOCOL,
        "construction": {
            "permutation_zero_based": INFLATABLE_PERMUTATION.tolist(),
            "iid_points": True,
            "exchangeable_projective_ergodic": True,
            "non_uniform_support": "seventeen diagonal permutation cells",
            "literature_exact_three_symmetry": True,
        },
        "rows": rows,
        "gates": {
            "rank_2_acceptance_at_least_0p90": by_rank[2]["acceptance_rate"] >= 0.90,
            "rank_3_acceptance_at_least_0p90": by_rank[3]["acceptance_rate"] >= 0.90,
            "rank_4_acceptance_zero": by_rank[4]["acceptance_rate"] == 0.0,
        },
        "conclusion": (
            "all rank-three permutation patterns, hence their induced product-order "
            "posets, match exactly; rank four separates the non-uniform permuton"
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
