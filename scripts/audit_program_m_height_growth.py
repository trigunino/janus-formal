"""MF-MAN-018: order-only height-growth gate against bounded-height kernels."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_ensemble_moment_adversary import antichain, total_order
    from scripts.audit_program_m_ensemble_separation import (
        PROTOCOL as SEPARATION_PROTOCOL,
        accepts as moment_gate_accepts,
        ensemble_statistics,
        minkowski_order,
    )
    from scripts.audit_program_m_ergodic_layer_adversary import layered_order
except ModuleNotFoundError:
    from audit_program_m_ensemble_moment_adversary import antichain, total_order
    from audit_program_m_ensemble_separation import (
        PROTOCOL as SEPARATION_PROTOCOL,
        accepts as moment_gate_accepts,
        ensemble_statistics,
        minkowski_order,
    )
    from audit_program_m_ergodic_layer_adversary import layered_order


PROTOCOL = {
    "protocol_id": "MF-MAN-018-v1",
    "base_seed": 2026071805,
    "validation_sizes": [288, 576, 1152, 2304],
    "replicates_per_model": 64,
    "height_ratio_min": 2.0,
    "derivation": (
        "fixed midpoint below Minkowski-1+1 sqrt(n) ratio sqrt(8) and "
        "above the bounded-height ratio 1"
    ),
    "frozen_moment_gate": SEPARATION_PROTOCOL["successor_rule"],
}


def order_height(order: np.ndarray) -> int:
    """Longest strict chain, computed from a supplied transitive order only."""
    strict = np.asarray(order, dtype=bool).copy()
    np.fill_diagonal(strict, False)
    height = np.ones(len(strict), dtype=np.int64)
    # If x<y, the strict past of y contains x and the strict past of x.
    topological_order = np.argsort(np.count_nonzero(strict, axis=0), kind="stable")
    for vertex in topological_order:
        predecessors = np.flatnonzero(strict[:, vertex])
        if len(predecessors):
            height[vertex] = 1 + int(np.max(height[predecessors]))
    return int(np.max(height, initial=0))


GENERATORS = {
    "minkowski_1p1": minkowski_order,
    "ergodic_six_level": layered_order,
    "total_order": total_order,
    "antichain": antichain,
}


def run_audit() -> dict[str, object]:
    model_rows = []
    sizes = PROTOCOL["validation_sizes"]
    for model_index, (model, generator) in enumerate(GENERATORS.items()):
        samples = []
        for replicate in range(int(PROTOCOL["replicates_per_model"])):
            heights = []
            moment_acceptance = []
            for size_index, size in enumerate(sizes):
                seed = (
                    int(PROTOCOL["base_seed"])
                    + 100_000_000 * model_index
                    + 100_000 * size_index
                    + replicate
                )
                order = generator(size, np.random.default_rng(seed))
                heights.append(order_height(order))
                moment_acceptance.append(
                    moment_gate_accepts(
                        ensemble_statistics(order), PROTOCOL["frozen_moment_gate"]
                    )
                )
            ratio = heights[-1] / heights[0]
            height_accepted = ratio > PROTOCOL["height_ratio_min"]
            samples.append(
                {
                    "heights": heights,
                    "largest_to_smallest_ratio": ratio,
                    "height_accepted": height_accepted,
                    "all_moment_gates_accepted": all(moment_acceptance),
                    "combined_accepted": height_accepted and all(moment_acceptance),
                }
            )
        model_rows.append(
            {
                "model": model,
                "replicates": len(samples),
                "mean_heights": np.mean(
                    np.array([sample["heights"] for sample in samples]), axis=0
                ).tolist(),
                "mean_height_ratio": float(
                    np.mean([sample["largest_to_smallest_ratio"] for sample in samples])
                ),
                "height_acceptance_rate": float(
                    np.mean([sample["height_accepted"] for sample in samples])
                ),
                "combined_acceptance_rate": float(
                    np.mean([sample["combined_accepted"] for sample in samples])
                ),
            }
        )
    by_model = {row["model"]: row for row in model_rows}
    return {
        "program": "MF-MAN-018",
        "protocol": PROTOCOL,
        "rows": model_rows,
        "gates": {
            "target_combined_acceptance_at_least_0p90":
                by_model["minkowski_1p1"]["combined_acceptance_rate"] >= 0.90,
            "six_level_combined_acceptance_zero":
                by_model["ergodic_six_level"]["combined_acceptance_rate"] == 0.0,
            "total_order_combined_acceptance_zero":
                by_model["total_order"]["combined_acceptance_rate"] == 0.0,
            "antichain_combined_acceptance_zero":
                by_model["antichain"]["combined_acceptance_rate"] == 0.0,
        },
        "scope": (
            "necessary unbounded-height diagnostic; growth alone is not dimension, "
            "manifold-likeness, metric reconstruction, or geometric uniqueness"
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

