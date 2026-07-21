"""MF-PAT-002: pre-registered ladder of complete induced-poset laws."""

from __future__ import annotations

import argparse
import functools
import itertools
import json
import math
from collections import Counter
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_decorated_layer_adversary import decorated_layer_order
    from scripts.audit_program_m_ensemble_separation import minkowski_order
except ModuleNotFoundError:
    from audit_program_m_decorated_layer_adversary import decorated_layer_order
    from audit_program_m_ensemble_separation import minkowski_order


PROTOCOL = {
    "protocol_id": "MF-PAT-002-v1",
    "ranks": [2, 3, 4, 5],
    "base_seed": 2026071810,
    "samples_per_batch": 512,
    "calibration_batches": 99,
    "validation_batches_per_model": 32,
    "family_alpha": 0.05,
    "per_rank_alpha": 0.0125,
    "upper_rank": 99,
}


def relation_mask(order: np.ndarray) -> int:
    return sum(1 << i for i, value in enumerate(order.ravel()) if value)


@functools.lru_cache(maxsize=None)
def permutations(rank: int) -> tuple[tuple[int, ...], ...]:
    return tuple(itertools.permutations(range(rank)))


@functools.lru_cache(maxsize=None)
def canonical_mask(rank: int, mask: int) -> int:
    matrix = np.array(
        [bool(mask & (1 << i)) for i in range(rank * rank)], dtype=bool
    ).reshape(rank, rank)
    return min(
        relation_mask(matrix[np.ix_(permutation, permutation)])
        for permutation in permutations(rank)
    )


def exact_minkowski_distribution(rank: int) -> dict[int, float]:
    counts: Counter[int] = Counter()
    first_rank = np.arange(rank)
    for second_rank in permutations(rank):
        points = np.column_stack((first_rank, np.array(second_rank)))
        order = np.all(points[:, None, :] <= points[None, :, :], axis=2)
        counts[canonical_mask(rank, relation_mask(order))] += 1
    denominator = math.factorial(rank)
    return {pattern: count / denominator for pattern, count in counts.items()}


def sampled_distribution(generator, rank: int, samples: int, seed: int) -> dict[int, float]:
    rng = np.random.default_rng(seed)
    counts: Counter[int] = Counter()
    for _ in range(samples):
        order = generator(rank, rng)
        counts[canonical_mask(rank, relation_mask(order))] += 1
    return {pattern: count / samples for pattern, count in counts.items()}


def total_variation(left: dict[int, float], right: dict[int, float]) -> float:
    return 0.5 * sum(
        abs(left.get(key, 0.0) - right.get(key, 0.0))
        for key in left.keys() | right.keys()
    )


def run_audit() -> dict[str, object]:
    samples = int(PROTOCOL["samples_per_batch"])
    rank_rows = []
    for rank in PROTOCOL["ranks"]:
        reference = exact_minkowski_distribution(rank)
        calibration = sorted(
            total_variation(
                sampled_distribution(
                    minkowski_order,
                    rank,
                    samples,
                    int(PROTOCOL["base_seed"]) + 100_000 * rank + batch,
                ),
                reference,
            )
            for batch in range(int(PROTOCOL["calibration_batches"]))
        )
        threshold = calibration[int(PROTOCOL["upper_rank"]) - 1]
        models = []
        for model_index, (name, generator) in enumerate(
            (("minkowski_1p1", minkowski_order), ("decorated_layer", decorated_layer_order))
        ):
            distances = [
                total_variation(
                    sampled_distribution(
                        generator,
                        rank,
                        samples,
                        int(PROTOCOL["base_seed"])
                        + 10_000_000 * (model_index + 1)
                        + 100_000 * rank
                        + batch,
                    ),
                    reference,
                )
                for batch in range(int(PROTOCOL["validation_batches_per_model"]))
            ]
            models.append(
                {
                    "model": name,
                    "mean_total_variation": float(np.mean(distances)),
                    "acceptance_rate": float(np.mean(np.array(distances) <= threshold)),
                }
            )
        rank_rows.append(
            {
                "rank": rank,
                "reference_pattern_count": len(reference),
                "threshold_total_variation": threshold,
                "models": models,
            }
        )
    decorated = [
        next(model for model in row["models"] if model["model"] == "decorated_layer")
        for row in rank_rows
    ]
    first_separating_rank = next(
        (row["rank"] for row, model in zip(rank_rows, decorated) if model["acceptance_rate"] == 0.0),
        None,
    )
    return {
        "program": "MF-PAT-002",
        "protocol": PROTOCOL,
        "rank_rows": rank_rows,
        "first_rank_with_zero_adversary_acceptance": first_separating_rank,
        "scope": (
            "fixed finite ladder with Bonferroni family error control; it does not "
            "claim that any finite terminal rank identifies the generating kernel"
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
