"""MF-ADV-007: ergodic infinite-level attack with square-root height growth."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_ensemble_separation import (
        accepts as moment_gate_accepts,
        ensemble_statistics,
    )
    from scripts.audit_program_m_height_growth import PROTOCOL as HEIGHT_PROTOCOL, order_height
except ModuleNotFoundError:
    from audit_program_m_ensemble_separation import (
        accepts as moment_gate_accepts,
        ensemble_statistics,
    )
    from audit_program_m_height_growth import PROTOCOL as HEIGHT_PROTOCOL, order_height


ATOM_LARGE = 0.6916876368964443677270353220185915
ATOM_SMALL = 0.03057593132024793078956501273897145
TAIL_MASS = 0.2165845691428118399042696397644941
BRANCH_WEIGHTS = np.array(
    [ATOM_LARGE, ATOM_SMALL, ATOM_SMALL, ATOM_SMALL, TAIL_MASS], dtype=float
)
BRANCH_WEIGHTS /= BRANCH_WEIGHTS.sum()

PROTOCOL = {
    "protocol_id": "MF-ADV-007-v1",
    "base_seed": 2026071806,
    "validation_sizes": [336, 672, 1344, 2688],
    "replicates": 64,
    "frozen_moment_gate": HEIGHT_PROTOCOL["frozen_moment_gate"],
    "frozen_height_ratio_min": HEIGHT_PROTOCOL["height_ratio_min"],
    "tail": "conditional Zipf exponent 2 over ordered levels 4,5,...",
}


def infinite_layer_order(size: int, rng: np.random.Generator) -> np.ndarray:
    branch = rng.choice(5, size=size, p=BRANCH_WEIGHTS)
    levels = branch.astype(np.int64)
    tail = branch == 4
    levels[tail] = 3 + rng.zipf(2.0, int(np.count_nonzero(tail)))
    order = levels[:, None] < levels[None, :]
    np.fill_diagonal(order, True)
    return order


def run_audit() -> dict[str, object]:
    samples = []
    for replicate in range(int(PROTOCOL["replicates"])):
        heights = []
        moment_acceptance = []
        statistics_by_size = []
        for size_index, size in enumerate(PROTOCOL["validation_sizes"]):
            seed = int(PROTOCOL["base_seed"]) + 100_000 * size_index + replicate
            order = infinite_layer_order(size, np.random.default_rng(seed))
            statistics = ensemble_statistics(order)
            statistics_by_size.append(statistics)
            heights.append(order_height(order))
            moment_acceptance.append(
                moment_gate_accepts(statistics, PROTOCOL["frozen_moment_gate"])
            )
        ratio = heights[-1] / heights[0]
        samples.append(
            {
                "heights": heights,
                "height_ratio": ratio,
                "all_moment_gates_accepted": all(moment_acceptance),
                "combined_accepted": all(moment_acceptance)
                and ratio > PROTOCOL["frozen_height_ratio_min"],
                "statistics": statistics_by_size,
            }
        )
    square_sum = ATOM_LARGE**2 + 3 * ATOM_SMALL**2 + (2 / 5) * TAIL_MASS**2
    cube_sum = ATOM_LARGE**3 + 3 * ATOM_SMALL**3 + (8 / 35) * TAIL_MASS**3
    accepted = sum(sample["combined_accepted"] for sample in samples)
    return {
        "program": "MF-ADV-007",
        "protocol": PROTOCOL,
        "analytic_properties": {
            "zipf_normalized_square_sum": 2 / 5,
            "zipf_normalized_cube_sum": 8 / 35,
            "level_square_sum": square_sum,
            "level_cube_sum": cube_sum,
            "limiting_pair_fraction": 1 - square_sum,
            "limiting_three_chain_fraction": 1 - 3 * square_sum + 2 * cube_sum,
            "occupied_level_growth": "order sqrt(n) from the exponent-2 occupancy tail",
            "exchangeable_projective_ergodic": True,
        },
        "summary": {
            "accepted": accepted,
            "generated": len(samples),
            "acceptance_rate": accepted / len(samples),
            "mean_heights": np.mean(
                np.array([sample["heights"] for sample in samples]), axis=0
            ).tolist(),
            "mean_height_ratio": float(np.mean([sample["height_ratio"] for sample in samples])),
            "minimum_height_ratio": min(sample["height_ratio"] for sample in samples),
            "maximum_height_ratio": max(sample["height_ratio"] for sample in samples),
        },
        "gates": {
            "moment_residual_below_1e_minus_12": max(
                abs(square_sum - 0.5), abs(cube_sum - 1 / 3)
            ) < 1e-12,
            "frozen_combined_gate_broken": accepted > 0,
        },
        "conclusion": (
            "an iid infinite-layer kernel matches both moments and square-root height; "
            "the current three-statistic gate is not sufficient"
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

