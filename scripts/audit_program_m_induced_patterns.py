"""MF-PAT-001: full induced four-point poset distribution gate."""

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


PATTERN_SIZE = 4
PERMUTATIONS = tuple(itertools.permutations(range(PATTERN_SIZE)))
PROTOCOL = {
    "protocol_id": "MF-PAT-001-v1",
    "pattern_size": PATTERN_SIZE,
    "base_seed": 2026071809,
    "samples_per_batch": 1024,
    "calibration_batches": 199,
    "validation_batches_per_model": 64,
    "alpha": 0.05,
    "upper_rank": 190,
    "reference": "exact 24 relative permutations of four iid product-order points",
}


def relation_mask(order: np.ndarray) -> int:
    matrix = np.asarray(order, dtype=bool)
    return sum(1 << index for index, value in enumerate(matrix.ravel()) if value)


@functools.lru_cache(maxsize=None)
def canonical_mask(mask: int) -> int:
    matrix = np.array(
        [bool(mask & (1 << index)) for index in range(PATTERN_SIZE**2)],
        dtype=bool,
    ).reshape(PATTERN_SIZE, PATTERN_SIZE)
    return min(relation_mask(matrix[np.ix_(permutation, permutation)]) for permutation in PERMUTATIONS)


def exact_minkowski_four_distribution() -> dict[int, float]:
    counts: Counter[int] = Counter()
    first_rank = np.arange(PATTERN_SIZE)
    for second_rank in PERMUTATIONS:
        points = np.column_stack((first_rank, np.array(second_rank)))
        order = np.all(points[:, None, :] <= points[None, :, :], axis=2)
        counts[canonical_mask(relation_mask(order))] += 1
    return {pattern: count / math.factorial(PATTERN_SIZE) for pattern, count in counts.items()}


def sampled_distribution(generator, samples: int, seed: int) -> dict[int, float]:
    rng = np.random.default_rng(seed)
    counts: Counter[int] = Counter()
    for _ in range(samples):
        order = generator(PATTERN_SIZE, rng)
        counts[canonical_mask(relation_mask(order))] += 1
    return {pattern: count / samples for pattern, count in counts.items()}


def total_variation(left: dict[int, float], right: dict[int, float]) -> float:
    return 0.5 * sum(abs(left.get(key, 0.0) - right.get(key, 0.0)) for key in left.keys() | right.keys())


def run_audit() -> dict[str, object]:
    reference = exact_minkowski_four_distribution()
    samples = int(PROTOCOL["samples_per_batch"])
    calibration = sorted(
        total_variation(
            sampled_distribution(
                minkowski_order,
                samples,
                int(PROTOCOL["base_seed"]) + batch,
            ),
            reference,
        )
        for batch in range(int(PROTOCOL["calibration_batches"]))
    )
    threshold = calibration[int(PROTOCOL["upper_rank"]) - 1]
    rows = []
    for model_index, (model, generator) in enumerate(
        (("minkowski_1p1", minkowski_order), ("decorated_layer", decorated_layer_order))
    ):
        distances = []
        for batch in range(int(PROTOCOL["validation_batches_per_model"])):
            seed = (
                int(PROTOCOL["base_seed"])
                + 10_000_000 * (model_index + 1)
                + batch
            )
            distances.append(
                total_variation(
                    sampled_distribution(generator, samples, seed), reference
                )
            )
        rows.append(
            {
                "model": model,
                "batches": len(distances),
                "mean_total_variation": float(np.mean(distances)),
                "minimum_total_variation": min(distances),
                "maximum_total_variation": max(distances),
                "acceptance_rate": float(np.mean(np.array(distances) <= threshold)),
            }
        )
    by_model = {row["model"]: row for row in rows}
    return {
        "program": "MF-PAT-001",
        "protocol": PROTOCOL,
        "exact_reference": {
            "unlabelled_pattern_count": len(reference),
            "probabilities": {str(key): value for key, value in sorted(reference.items())},
            "probability_sum": sum(reference.values()),
        },
        "calibration": {
            "threshold_total_variation": threshold,
            "coverage_at_threshold": sum(value <= threshold for value in calibration)
            / len(calibration),
        },
        "rows": rows,
        "gates": {
            "all_16_four_point_posets_present_in_reference": len(reference) == 16,
            "target_validation_coverage_at_least_0p90":
                by_model["minkowski_1p1"]["acceptance_rate"] >= 0.90,
            "decorated_adversary_acceptance_zero":
                by_model["decorated_layer"]["acceptance_rate"] == 0.0,
        },
        "scope": (
            "complete induced distribution at rank four only; the hierarchy over "
            "all finite ranks, not one fixed rank, is the identifying object"
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

