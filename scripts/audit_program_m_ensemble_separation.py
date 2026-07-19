"""MF-ENS-002: first held-out ensemble separation experiment.

The target is the fixed-cardinality law of iid uniform points in a 1+1
Minkowski diamond (product order in null coordinates).  The competitor is an
exchangeable two-level order.  It is deliberately calibrated to have the same
limiting pair-ordering fraction, so the separation must use higher structure.
"""

from __future__ import annotations

import argparse
import json
from math import comb
from pathlib import Path

import numpy as np


PROTOCOL = {
    "protocol_id": "MF-ENS-002-v1",
    "base_seed": 2026071802,
    "training_sizes": [32, 64],
    "failed_pilot_validation_sizes": [128, 256, 512, 1024],
    "successor_validation_sizes": [160, 320, 640, 1280],
    "replicates_per_model_and_size": 64,
    "failed_pilot_rule": {
        "pair_fraction_interval": [0.40, 0.60],
        "three_chain_fraction_min_exclusive": 1 / 6,
    },
    "successor_rule": {
        "pair_fraction_interval": [0.40, 0.60],
        "three_chain_fraction_min_exclusive": 1 / 12,
        "derivation": "midpoint of the corrected exact limits 1/6 and 0",
    },
}


def minkowski_order(size: int, rng: np.random.Generator) -> np.ndarray:
    """Fixed-n iid sprinkling in a null-coordinate unit diamond."""
    points = rng.random((size, 2))
    order = np.all(points[:, None, :] <= points[None, :, :], axis=2)
    np.fill_diagonal(order, True)
    return order


def matched_two_level_order(size: int, rng: np.random.Generator) -> np.ndarray:
    """Exchangeable projective non-manifold competitor with matched pair density."""
    upper = rng.integers(0, 2, size=size, dtype=np.int8).astype(bool)
    order = (~upper[:, None]) & upper[None, :]
    np.fill_diagonal(order, True)
    return order


def ensemble_statistics(order: np.ndarray) -> dict[str, float]:
    matrix = np.asarray(order, dtype=bool)
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError("order must be square")
    size = matrix.shape[0]
    strict = matrix.copy()
    np.fill_diagonal(strict, False)
    pair_fraction = (
        float(np.count_nonzero(strict)) / comb(size, 2) if size >= 2 else 0.0
    )
    # Every strict three-chain has exactly one middle element.
    past = np.count_nonzero(strict, axis=0).astype(np.int64)
    future = np.count_nonzero(strict, axis=1).astype(np.int64)
    three_chains = int(np.dot(past, future))
    three_chain_fraction = three_chains / comb(size, 3) if size >= 3 else 0.0
    return {
        "pair_fraction": pair_fraction,
        "three_chain_fraction": three_chain_fraction,
    }


def accepts(statistics: dict[str, float], rule: dict[str, object]) -> bool:
    lower, upper = rule["pair_fraction_interval"]
    return bool(
        lower <= statistics["pair_fraction"] <= upper
        and statistics["three_chain_fraction"]
        > rule["three_chain_fraction_min_exclusive"]
    )


def _evaluate(
    model: str, size: int, seed_offset: int, phase: str, rule: dict[str, object]
) -> dict[str, object]:
    generator = minkowski_order if model == "minkowski_1p1" else matched_two_level_order
    samples = []
    for replicate in range(int(PROTOCOL["replicates_per_model_and_size"])):
        seed = int(PROTOCOL["base_seed"]) + seed_offset + replicate
        statistics = ensemble_statistics(generator(size, np.random.default_rng(seed)))
        samples.append({**statistics, "accepted": accepts(statistics, rule)})
    return {
        "phase": phase,
        "model": model,
        "size": size,
        "replicates": len(samples),
        "acceptance_rate": float(np.mean([sample["accepted"] for sample in samples])),
        "mean_pair_fraction": float(np.mean([sample["pair_fraction"] for sample in samples])),
        "mean_three_chain_fraction": float(
            np.mean([sample["three_chain_fraction"] for sample in samples])
        ),
    }


def run_audit() -> dict[str, object]:
    rows = []
    phases = (
        ("training", PROTOCOL["training_sizes"], PROTOCOL["failed_pilot_rule"], 0),
        (
            "failed_pilot_validation",
            PROTOCOL["failed_pilot_validation_sizes"],
            PROTOCOL["failed_pilot_rule"],
            10_000_000,
        ),
        (
            "successor_validation",
            PROTOCOL["successor_validation_sizes"],
            PROTOCOL["successor_rule"],
            20_000_000,
        ),
    )
    for model_index, model in enumerate(("minkowski_1p1", "matched_two_level")):
        for phase, sizes, rule, phase_offset in phases:
            for size_index, size in enumerate(sizes):
                rows.append(
                    _evaluate(
                        model,
                        size,
                        100_000_000 * model_index + phase_offset + 100_000 * size_index,
                        phase,
                        rule,
                    )
                )
    pilot = [row for row in rows if row["phase"] == "failed_pilot_validation"]
    successor = [row for row in rows if row["phase"] == "successor_validation"]
    pilot_target = [row for row in pilot if row["model"] == "minkowski_1p1"]
    target = [row for row in successor if row["model"] == "minkowski_1p1"]
    competitor = [row for row in successor if row["model"] == "matched_two_level"]
    return {
        "program": "MF-ENS-002",
        "protocol": PROTOCOL,
        "analytic_references": {
            "both_limiting_pair_fraction": 0.5,
            "minkowski_limiting_three_chain_fraction": 1 / 6,
            "two_level_three_chain_fraction": 0.0,
        },
        "rows": rows,
        "gates": {
            "all_size_sets_disjoint": len(
                set(PROTOCOL["training_sizes"])
                | set(PROTOCOL["failed_pilot_validation_sizes"])
                | set(PROTOCOL["successor_validation_sizes"])
            ) == sum(len(sizes) for _, sizes, _, _ in phases),
            "failed_pilot_target_rate_below_0p95_retained": any(
                row["acceptance_rate"] < 0.95 for row in pilot_target
            ),
            "successor_target_all_validation_rates_at_least_0p95": all(
                row["acceptance_rate"] >= 0.95 for row in target
            ),
            "successor_competitor_all_validation_rates_zero": all(
                row["acceptance_rate"] == 0.0 for row in competitor
            ),
        },
        "scope": (
            "finite evidence for one declared pair of exchangeable projective laws; "
            "not a proof of geometric uniqueness or the MF-ENS-001 asymptotic limits"
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
