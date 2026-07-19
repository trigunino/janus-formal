"""MF-ADV-008: infinite-layer attack decorated by random height-two micro-orders."""

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
    from scripts.audit_program_m_exact_twins import largest_twin_class
    from scripts.audit_program_m_height_growth import order_height
    from scripts.audit_program_m_twin_fraction_decay import PROTOCOL as TWIN_PROTOCOL
except ModuleNotFoundError:
    from audit_program_m_ensemble_separation import (
        accepts as moment_gate_accepts,
        ensemble_statistics,
    )
    from audit_program_m_exact_twins import largest_twin_class
    from audit_program_m_height_growth import order_height
    from audit_program_m_twin_fraction_decay import PROTOCOL as TWIN_PROTOCOL


ATOM_LARGE = 0.7301045571888240201090645605077272
ATOM_SMALL = 0.01161766540800840900937877540917690
TAIL_MASS = 0.2350424465871507528627991132647421
MICRO_EDGE_PROBABILITY = 0.2
BRANCH_WEIGHTS = np.array(
    [ATOM_LARGE, ATOM_SMALL, ATOM_SMALL, ATOM_SMALL, TAIL_MASS], dtype=float
)
BRANCH_WEIGHTS /= BRANCH_WEIGHTS.sum()

PROTOCOL = {
    "protocol_id": "MF-ADV-008-v1",
    "base_seed": 2026071808,
    "validation_sizes": [432, 864, 1728, 3456],
    "replicates": 64,
    "micro_edge_probability": MICRO_EDGE_PROBABILITY,
    "frozen_moment_gate": TWIN_PROTOCOL["frozen_moment_gate"],
    "frozen_height_ratio_min": TWIN_PROTOCOL["frozen_height_ratio_min"],
    "frozen_twin_fraction_ratio_max_exclusive":
        TWIN_PROTOCOL["largest_twin_fraction_ratio_max_exclusive"],
}


def decorated_layer_order(size: int, rng: np.random.Generator) -> np.ndarray:
    branch = rng.choice(5, size=size, p=BRANCH_WEIGHTS)
    levels = branch.astype(np.int64)
    tail = branch == 4
    levels[tail] = 3 + rng.zipf(2.0, int(np.count_nonzero(tail)))
    upper = rng.integers(0, 2, size=size, dtype=np.int8).astype(bool)
    order = levels[:, None] < levels[None, :]
    for level in np.unique(levels):
        members = np.flatnonzero(levels == level)
        lower_members = members[~upper[members]]
        upper_members = members[upper[members]]
        if len(lower_members) and len(upper_members):
            edges = rng.random((len(lower_members), len(upper_members))) < MICRO_EDGE_PROBABILITY
            order[np.ix_(lower_members, upper_members)] = edges
    np.fill_diagonal(order, True)
    return order


def run_audit() -> dict[str, object]:
    samples = []
    sizes = PROTOCOL["validation_sizes"]
    for replicate in range(int(PROTOCOL["replicates"])):
        heights = []
        twin_fractions = []
        moment_acceptance = []
        for size_index, size in enumerate(sizes):
            seed = int(PROTOCOL["base_seed"]) + 100_000 * size_index + replicate
            order = decorated_layer_order(size, np.random.default_rng(seed))
            heights.append(order_height(order))
            twin_fractions.append(largest_twin_class(order) / size)
            moment_acceptance.append(
                moment_gate_accepts(
                    ensemble_statistics(order), PROTOCOL["frozen_moment_gate"]
                )
            )
        height_ratio = heights[-1] / heights[0]
        twin_ratio = twin_fractions[-1] / twin_fractions[0]
        samples.append(
            {
                "heights": heights,
                "height_ratio": height_ratio,
                "largest_twin_fractions": twin_fractions,
                "twin_fraction_ratio": twin_ratio,
                "combined_accepted": all(moment_acceptance)
                and height_ratio > PROTOCOL["frozen_height_ratio_min"]
                and twin_ratio
                < PROTOCOL["frozen_twin_fraction_ratio_max_exclusive"],
            }
        )
    p = MICRO_EDGE_PROBABILITY
    square_sum = ATOM_LARGE**2 + 3 * ATOM_SMALL**2 + (2 / 5) * TAIL_MASS**2
    cube_sum = ATOM_LARGE**3 + 3 * ATOM_SMALL**3 + (8 / 35) * TAIL_MASS**3
    pair = 1 - (1 - p / 2) * square_sum
    triples = 1 - 3 * square_sum + 2 * cube_sum + (3 * p / 2) * (
        square_sum - cube_sum
    )
    accepted = sum(sample["combined_accepted"] for sample in samples)
    return {
        "program": "MF-ADV-008",
        "protocol": PROTOCOL,
        "analytic_properties": {
            "level_square_sum": square_sum,
            "level_cube_sum": cube_sum,
            "limiting_pair_fraction": pair,
            "limiting_three_chain_fraction": triples,
            "exchangeable_projective_ergodic": True,
            "microstructure": "independent random height-two order inside every level",
        },
        "summary": {
            "generated": len(samples),
            "accepted": accepted,
            "acceptance_rate": accepted / len(samples),
            "mean_heights": np.mean(
                np.array([sample["heights"] for sample in samples]), axis=0
            ).tolist(),
            "mean_height_ratio": float(np.mean([sample["height_ratio"] for sample in samples])),
            "mean_largest_twin_fractions": np.mean(
                np.array([sample["largest_twin_fractions"] for sample in samples]), axis=0
            ).tolist(),
            "mean_twin_fraction_ratio": float(
                np.mean([sample["twin_fraction_ratio"] for sample in samples])
            ),
        },
        "gates": {
            "moment_residual_below_1e_minus_12":
                max(abs(pair - 0.5), abs(triples - 1 / 6)) < 1e-12,
            "frozen_four_diagnostic_gate_broken": accepted > 0,
        },
        "conclusion": (
            "random within-level microstructure removes macroscopic exact twins "
            "while retaining matched moments and square-root height"
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

