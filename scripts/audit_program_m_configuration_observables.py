"""MF-OBS-001: finite audit of invariant configuration observables."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import numpy as np


def relabel(relation: np.ndarray, permutation: tuple[int, ...]) -> np.ndarray:
    return relation[np.ix_(permutation, permutation)]


def relation_from_mask(mask: int, size: int = 2) -> np.ndarray:
    return np.array(
        [[bool(mask & (1 << (size * left + right))) for right in range(size)]
         for left in range(size)],
        dtype=bool,
    )


def observable_is_invariant(observable) -> bool:
    permutations = list(itertools.permutations(range(2)))
    return all(
        observable(relabel(relation_from_mask(mask), permutation))
        == observable(relation_from_mask(mask))
        for mask in range(16) for permutation in permutations
    )


def run_audit() -> dict[str, object]:
    observables = {
        "edge_count": lambda relation: int(np.count_nonzero(relation)),
        "loop_count": lambda relation: int(np.count_nonzero(np.diag(relation))),
        "mutual_pair_count": lambda relation: int(relation[0, 1] and relation[1, 0]),
        "label_zero_out_degree": lambda relation: int(np.count_nonzero(relation[0])),
    }
    results = {name: observable_is_invariant(observable) for name, observable in observables.items()}
    return {
        "program": "MF-OBS-001",
        "census": "all 16 binary relations on two labelled objects and both relabellings",
        "observables": results,
        "gates": {
            "structural_counts_are_invariant": all(
                results[name] for name in ("edge_count", "loop_count", "mutual_pair_count")
            ),
            "label_dependent_probe_is_rejected": not results["label_zero_out_degree"],
        },
        "scope": (
            "interface and invariance criterion only; no observable is promoted to a "
            "physical action or preferred selector"
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
