"""MF-DESC-001: primitive descent and generated reachability audit."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import numpy as np


def reflexive_transitive_closure(relation: np.ndarray) -> np.ndarray:
    closure = np.asarray(relation, dtype=bool).copy()
    np.fill_diagonal(closure, True)
    for middle in range(len(closure)):
        closure |= closure[:, middle, None] & closure[None, middle, :]
    return closure


def run_audit() -> dict[str, object]:
    local_edge = np.array([[False, True], [False, False]], dtype=bool)
    patches = ((local_edge, (0, 1)), (local_edge, (1, 2)))
    locally_witnessed = np.zeros((3, 3), dtype=bool)
    covered_pairs = set()
    for relation, embedding in patches:
        for left, right in itertools.product(range(2), repeat=2):
            global_pair = (embedding[left], embedding[right])
            covered_pairs.add(global_pair)
            if relation[left, right]:
                locally_witnessed[global_pair] = True

    uncovered_pairs = sorted(set(itertools.product(range(3), repeat=2)) - covered_pairs)
    compatible_globals = []
    for values in itertools.product((False, True), repeat=len(uncovered_pairs)):
        candidate = locally_witnessed.copy()
        for pair, value in zip(uncovered_pairs, values, strict=True):
            candidate[pair] = value
        compatible_globals.append(candidate)
    descent_globals = [
        candidate for candidate in compatible_globals
        if np.array_equal(candidate, locally_witnessed)
    ]
    reachability = reflexive_transitive_closure(locally_witnessed)
    return {
        "program": "MF-DESC-001",
        "example": {
            "patches": 2,
            "global_points": 3,
            "locally_witnessed_primitive_relations": int(np.count_nonzero(locally_witnessed)),
            "uncovered_ordered_pairs": [list(pair) for pair in uncovered_pairs],
            "globals_compatible_with_restrictions_only": len(compatible_globals),
            "globals_satisfying_primitive_descent": len(descent_globals),
            "reachability_relations_including_reflexivity": int(np.count_nonzero(reachability)),
        },
        "gates": {
            "local_restrictions_alone_are_not_unique": len(compatible_globals) == 4,
            "primitive_descent_selects_unique_free_global": len(descent_globals) == 1,
            "endpoint_relation_is_not_primitive": not bool(locally_witnessed[0, 2]),
            "endpoint_is_globally_reachable": bool(reachability[0, 2]),
        },
        "conclusion": (
            "primitive descent yields the unique minimal relation, while global "
            "reachability must be reconstructed after gluing and can cross patches"
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
