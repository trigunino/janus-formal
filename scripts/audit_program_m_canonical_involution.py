"""MF-INV-001: audit whether a relation canonically selects an involution."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


Permutation = tuple[int, ...]


def compose(left: Permutation, right: Permutation) -> Permutation:
    return tuple(left[right[x]] for x in range(len(left)))


def relabel(mask: int, size: int, permutation: Permutation) -> int:
    return sum(
        1 << (size * permutation[source] + permutation[target])
        for source in range(size)
        for target in range(size)
        if mask & (1 << (size * source + target))
    )


def automorphisms(mask: int, size: int) -> tuple[Permutation, ...]:
    return tuple(
        permutation
        for permutation in itertools.permutations(range(size))
        if relabel(mask, size, permutation) == mask
    )


def canonical_involutions(mask: int, size: int) -> tuple[Permutation, ...]:
    identity = tuple(range(size))
    symmetries = automorphisms(mask, size)
    involutions = tuple(p for p in symmetries if compose(p, p) == identity)
    return tuple(
        p
        for p in involutions
        if all(compose(p, a) == compose(a, p) for a in symmetries)
    )


def run_audit() -> dict[str, object]:
    size = 3
    identity = tuple(range(size))
    rows = []
    for mask in range(1 << (size * size)):
        symmetries = automorphisms(mask, size)
        involutions = tuple(p for p in symmetries if compose(p, p) == identity)
        central = canonical_involutions(mask, size)
        rows.append(
            {
                "has_nontrivial_involution": any(p != identity for p in involutions),
                "has_nontrivial_canonical_involution": any(p != identity for p in central),
            }
        )
    empty_aut = automorphisms(0, size)
    empty_involutions = tuple(p for p in empty_aut if compose(p, p) == identity)
    empty_canonical = canonical_involutions(0, size)
    return {
        "program": "MF-INV-001",
        "protocol": {"rank": size, "relations": len(rows)},
        "counts": {
            "relations_with_nontrivial_involution": sum(
                row["has_nontrivial_involution"] for row in rows
            ),
            "relations_with_nontrivial_canonical_involution": sum(
                row["has_nontrivial_canonical_involution"] for row in rows
            ),
        },
        "empty_relation_witness": {
            "automorphisms": [list(p) for p in empty_aut],
            "involutions": [list(p) for p in empty_involutions],
            "central_involutions": [list(p) for p in empty_canonical],
        },
        "gates": {
            "empty_relation_has_three_nontrivial_involutions": len(empty_involutions) == 4,
            "empty_relation_has_no_nontrivial_canonical_involution": empty_canonical == (identity,),
            "existence_does_not_imply_canonical_selection": any(
                row["has_nontrivial_involution"]
                and not row["has_nontrivial_canonical_involution"]
                for row in rows
            ),
        },
        "conclusion": (
            "a relation may admit nontrivial involutions without canonically "
            "selecting one; a natural choice must be central in its automorphism group"
        ),
        "scope": (
            "exact rank-three obstruction to a universal nontrivial intrinsic "
            "involution selector"
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
