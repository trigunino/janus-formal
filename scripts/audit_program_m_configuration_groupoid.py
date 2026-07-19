"""MF-CONF-001: finite audit of the relational configuration groupoid."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import numpy as np


ROOT = Path(__file__).resolve().parents[1]
LEAN_SOURCE = "JanusFormal/Foundations/ProgramMConfigurationGroupoid.lean"


def relabel(relation: np.ndarray, permutation: tuple[int, ...]) -> np.ndarray:
    return relation[np.ix_(permutation, permutation)]


def compose(
    first: tuple[int, ...], second: tuple[int, ...]
) -> tuple[int, ...]:
    return tuple(first[second[index]] for index in range(len(first)))


def inverse(permutation: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * len(permutation)
    for source, target in enumerate(permutation):
        result[target] = source
    return tuple(result)


def run_audit() -> dict[str, object]:
    relation = np.array(
        [[False, True, False], [False, False, True], [True, False, False]], dtype=bool
    )
    permutations = list(itertools.permutations(range(3)))
    automorphisms = [p for p in permutations if np.array_equal(relabel(relation, p), relation)]
    identity = tuple(range(3))
    closure = all(compose(left, right) in automorphisms for left in automorphisms for right in automorphisms)
    inverses = all(inverse(p) in automorphisms for p in automorphisms)
    associativity = all(
        compose(compose(a, b), c) == compose(a, compose(b, c))
        for a in automorphisms for b in automorphisms for c in automorphisms
    )
    edge_counts = {
        int(np.count_nonzero(relabel(relation, permutation))) for permutation in permutations
    }
    lean_text = (ROOT / LEAN_SOURCE).read_text(encoding="utf-8")
    theorem_names = ("refl_trans", "trans_refl", "trans_assoc", "trans_symm", "symm_trans")
    return {
        "program": "MF-CONF-001",
        "lean_source": LEAN_SOURCE,
        "finite_example": {
            "objects": 3,
            "automorphisms": [list(p) for p in automorphisms],
            "automorphism_count": len(automorphisms),
            "edge_count_orbit_values": sorted(edge_counts),
        },
        "gates": {
            "identity_present": identity in automorphisms,
            "composition_closed": closure,
            "inverses_present": inverses,
            "composition_associative": associativity,
            "edge_count_is_isomorphism_invariant": len(edge_counts) == 1,
            "lean_groupoid_laws_present": all(
                f"theorem {name}" in lean_text for name in theorem_names
            ),
        },
        "scope": (
            "configuration groupoid and invariant observables only; no topology, "
            "metric, dynamics, probability or physical action"
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
