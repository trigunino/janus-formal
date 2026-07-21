"""MF-WEIGHT-001: relational invariance does not select primitive weights."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


Edge = tuple[int, int]


def automorphisms(vertices: tuple[int, ...], edges: frozenset[Edge]) -> tuple[tuple[int, ...], ...]:
    return tuple(
        permutation
        for permutation in itertools.permutations(vertices)
        if {
            (permutation[source], permutation[target])
            for source, target in edges
        } == edges
    )


def invariant_weighting(
    edges: frozenset[Edge], permutation: tuple[int, ...], weights: dict[Edge, int]
) -> bool:
    return all(
        weights[(source, target)]
        == weights[(permutation[source], permutation[target])]
        for source, target in edges
    )


def run_audit() -> dict[str, object]:
    vertices = (0, 1, 2)
    edges = frozenset(((0, 1), (1, 2)))
    symmetries = automorphisms(vertices, edges)
    candidates = []
    for first, second in itertools.product(range(1, 4), repeat=2):
        weights = {(0, 1): first, (1, 2): second}
        invariant = all(
            invariant_weighting(edges, permutation, weights)
            for permutation in symmetries
        )
        candidates.append(
            {
                "edge_weights": [first, second],
                "distance_0_to_2": first + second,
                "automorphism_invariant": invariant,
                "glues_from_edge_patches": True,
            }
        )
    normalized = [row for row in candidates if row["edge_weights"][0] == 1]
    return {
        "program": "MF-WEIGHT-001",
        "witness": {
            "vertices": list(vertices),
            "primitive_edges": [list(edge) for edge in sorted(edges)],
            "automorphisms": [list(permutation) for permutation in symmetries],
            "patches": [[0, 1], [1, 2]],
        },
        "candidate_weightings": candidates,
        "counts": {
            "invariant_and_gluable": sum(
                row["automorphism_invariant"] and row["glues_from_edge_patches"]
                for row in candidates
            ),
            "after_fixing_first_edge_to_one": len(normalized),
            "distinct_normalized_ratios": len(
                {row["edge_weights"][1] for row in normalized}
            ),
        },
        "gates": {
            "chain_has_only_identity_automorphism": len(symmetries) == 1,
            "all_nine_weightings_are_invariant_and_gluable": all(
                row["automorphism_invariant"] and row["glues_from_edge_patches"]
                for row in candidates
            ),
            "relative_weight_ambiguity_survives_scale_fixing": len(normalized) == 3,
        },
        "conclusion": (
            "relations, relabelling invariance and gluing do not determine even "
            "relative primitive edge weights"
        ),
        "scope": (
            "exact finite no-go for weight selection from the declared structural "
            "principles; additional statistical or algebraic structure may select weights"
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
