"""MF-ADV-005: non-ergodic law matching the first two ensemble moments."""

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
        matched_two_level_order,
    )
except ModuleNotFoundError:
    from audit_program_m_ensemble_separation import (
        PROTOCOL as SEPARATION_PROTOCOL,
        accepts,
        ensemble_statistics,
        matched_two_level_order,
    )


PROTOCOL = {
    "protocol_id": "MF-ADV-005-v1",
    "base_seed": 2026071803,
    "validation_sizes": [192, 384, 768, 1536],
    "stratified_replicates": {
        "total_order": 10,
        "two_level": 40,
        "antichain": 10,
    },
    "mixture_weights": {
        "total_order": 1 / 6,
        "two_level": 2 / 3,
        "antichain": 1 / 6,
    },
    "frozen_gate": SEPARATION_PROTOCOL["successor_rule"],
}


def total_order(size: int, rng: np.random.Generator) -> np.ndarray:
    ranks = np.empty(size, dtype=np.int64)
    ranks[rng.permutation(size)] = np.arange(size)
    return ranks[:, None] <= ranks[None, :]


def antichain(size: int, _rng: np.random.Generator) -> np.ndarray:
    return np.eye(size, dtype=bool)


GENERATORS = {
    "total_order": total_order,
    "two_level": matched_two_level_order,
    "antichain": antichain,
}


def run_audit() -> dict[str, object]:
    rows = []
    for size_index, size in enumerate(PROTOCOL["validation_sizes"]):
        component_rows = []
        for component_index, (name, replicates) in enumerate(
            PROTOCOL["stratified_replicates"].items()
        ):
            samples = []
            for replicate in range(replicates):
                seed = (
                    int(PROTOCOL["base_seed"])
                    + 10_000_000 * size_index
                    + 100_000 * component_index
                    + replicate
                )
                statistics = ensemble_statistics(
                    GENERATORS[name](size, np.random.default_rng(seed))
                )
                samples.append(
                    {**statistics, "accepted": accepts(statistics, PROTOCOL["frozen_gate"])}
                )
            component_rows.append(
                {
                    "component": name,
                    "replicates": replicates,
                    "acceptance_rate": float(
                        np.mean([sample["accepted"] for sample in samples])
                    ),
                    "mean_pair_fraction": float(
                        np.mean([sample["pair_fraction"] for sample in samples])
                    ),
                    "mean_three_chain_fraction": float(
                        np.mean([sample["three_chain_fraction"] for sample in samples])
                    ),
                }
            )
        total = sum(PROTOCOL["stratified_replicates"].values())
        rows.append(
            {
                "size": size,
                "components": component_rows,
                "stratified_mixture_acceptance_rate": sum(
                    row["acceptance_rate"] * row["replicates"] for row in component_rows
                ) / total,
                "stratified_mean_pair_fraction": sum(
                    row["mean_pair_fraction"] * row["replicates"]
                    for row in component_rows
                ) / total,
                "stratified_mean_three_chain_fraction": sum(
                    row["mean_three_chain_fraction"] * row["replicates"]
                    for row in component_rows
                ) / total,
            }
        )
    return {
        "program": "MF-ADV-005",
        "protocol": PROTOCOL,
        "exact_mixture_moments": {
            "pair_fraction": 0.5,
            "three_chain_fraction": 1 / 6,
        },
        "rows": rows,
        "gates": {
            "matches_both_minkowski_moments_exactly_in_law": True,
            "frozen_gate_rejects_every_sample": all(
                row["stratified_mixture_acceptance_rate"] == 0.0 for row in rows
            ),
        },
        "conclusion": (
            "matching finitely many ensemble means does not identify the law; "
            "the frozen gate additionally detects concentration within each sample"
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

