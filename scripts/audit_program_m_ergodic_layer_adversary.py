"""MF-ADV-006: ergodic layered adversary matching two Minkowski moments."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_ensemble_separation import (
        PROTOCOL as SEPARATION_PROTOCOL,
        accepts,
        ensemble_statistics,
    )
except ModuleNotFoundError:
    from audit_program_m_ensemble_separation import (
        PROTOCOL as SEPARATION_PROTOCOL,
        accepts,
        ensemble_statistics,
    )


# Three rational coordinates were frozen first; the other three are positive
# roots of the resulting symmetric-moment equations, evaluated here to enough
# precision that numerical sampling error dominates the residual by many orders.
LEVEL_WEIGHTS = np.array(
    [
        0.0622080850525203905,
        0.6923271182573734216,
        0.0638335466901061879,
        0.032315000,
        0.058125380,
        0.091190870,
    ],
    dtype=float,
)
LEVEL_WEIGHTS /= LEVEL_WEIGHTS.sum()

PROTOCOL = {
    "protocol_id": "MF-ADV-006-v1",
    "base_seed": 2026071804,
    "validation_sizes": [224, 448, 896, 1792],
    "replicates_per_size": 64,
    "frozen_gate": SEPARATION_PROTOCOL["successor_rule"],
    "level_weights": LEVEL_WEIGHTS.tolist(),
}


def layered_order(size: int, rng: np.random.Generator) -> np.ndarray:
    levels = rng.choice(len(LEVEL_WEIGHTS), size=size, p=LEVEL_WEIGHTS)
    order = levels[:, None] < levels[None, :]
    np.fill_diagonal(order, True)
    return order


def longest_strict_chain(order: np.ndarray) -> int:
    strict = np.asarray(order, dtype=bool).copy()
    np.fill_diagonal(strict, False)
    height = np.ones(len(strict), dtype=np.int64)
    # The generated relation can be topologically sorted by predecessor count.
    for vertex in np.argsort(np.count_nonzero(strict, axis=0)):
        predecessors = np.flatnonzero(strict[:, vertex])
        if len(predecessors):
            height[vertex] = 1 + int(np.max(height[predecessors]))
    return int(np.max(height, initial=0))


def run_audit() -> dict[str, object]:
    rows = []
    for size_index, size in enumerate(PROTOCOL["validation_sizes"]):
        samples = []
        for replicate in range(int(PROTOCOL["replicates_per_size"])):
            seed = int(PROTOCOL["base_seed"]) + 100_000 * size_index + replicate
            order = layered_order(size, np.random.default_rng(seed))
            statistics = ensemble_statistics(order)
            samples.append(
                {
                    **statistics,
                    "height": longest_strict_chain(order),
                    "accepted": accepts(statistics, PROTOCOL["frozen_gate"]),
                }
            )
        rows.append(
            {
                "size": size,
                "replicates": len(samples),
                "acceptance_rate": float(np.mean([sample["accepted"] for sample in samples])),
                "mean_pair_fraction": float(np.mean([sample["pair_fraction"] for sample in samples])),
                "mean_three_chain_fraction": float(
                    np.mean([sample["three_chain_fraction"] for sample in samples])
                ),
                "maximum_height": max(sample["height"] for sample in samples),
            }
        )
    square_sum = float(np.sum(LEVEL_WEIGHTS**2))
    cube_sum = float(np.sum(LEVEL_WEIGHTS**3))
    return {
        "program": "MF-ADV-006",
        "protocol": PROTOCOL,
        "kernel_properties": {
            "iid_levels": True,
            "exchangeable": True,
            "projective": True,
            "ergodic_dissociated": True,
            "maximum_height": len(LEVEL_WEIGHTS),
        },
        "moment_residuals": {
            "sum_weights_minus_1": float(np.sum(LEVEL_WEIGHTS) - 1),
            "sum_squares_minus_1_over_2": square_sum - 0.5,
            "sum_cubes_minus_1_over_3": cube_sum - 1 / 3,
            "pair_fraction_minus_1_over_2": (1 - square_sum) - 0.5,
            "three_chain_fraction_minus_1_over_6":
                (1 - 3 * square_sum + 2 * cube_sum) - 1 / 6,
        },
        "rows": rows,
        "gates": {
            "analytic_residual_below_1e_minus_12": max(
                abs(value) for value in (
                    square_sum - 0.5,
                    cube_sum - 1 / 3,
                )
            ) < 1e-12,
            "frozen_gate_broken_on_every_size": all(
                row["acceptance_rate"] > 0 for row in rows
            ),
            "bounded_height_exposes_non_minkowski_structure": all(
                row["maximum_height"] <= len(LEVEL_WEIGHTS) for row in rows
            ),
        },
        "conclusion": (
            "the two-statistic MF-ENS-002 gate is broken by an iid ergodic "
            "six-level kernel; height scaling is the preregistered successor"
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

