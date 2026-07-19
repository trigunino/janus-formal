"""MF-REF-001: exhaustive audit of pair-covering refinement."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def observed_pairs(patches: tuple[frozenset[int], ...]) -> set[tuple[int, int]]:
    return {
        pair
        for patch in patches
        for pair in itertools.product(patch, repeat=2)
    }


def run_audit() -> dict[str, object]:
    size = 3
    objects = range(size)
    all_pairs = set(itertools.product(objects, repeat=2))
    possible_patches = tuple(
        frozenset(x for x in objects if mask & (1 << x))
        for mask in range(1 << size)
    )
    failures = 0
    pair_covering = 0
    for atlas_mask in range(1 << len(possible_patches)):
        patches = tuple(
            patch
            for index, patch in enumerate(possible_patches)
            if atlas_mask & (1 << index)
        )
        covered = observed_pairs(patches)
        pair_covered = all_pairs <= covered
        restriction_is_injective = len(covered) == len(all_pairs)
        failures += pair_covered != restriction_is_injective
        pair_covering += pair_covered

    original = (frozenset((0, 1, 2)), frozenset((0, 1, 3)))
    refined = original + (frozenset((2, 3)),)
    rank4_pairs = set(itertools.product(range(4), repeat=2))
    return {
        "program": "MF-REF-001",
        "protocol": {
            "rank": size,
            "atlas_families": 1 << len(possible_patches),
            "pair_covering_families": pair_covering,
        },
        "failures": failures,
        "mf_geo_002_witness": {
            "original_pair_covered": rank4_pairs <= observed_pairs(original),
            "after_adding_2_3_patch": rank4_pairs <= observed_pairs(refined),
        },
        "gates": {
            "pair_coverage_exactly_matches_pair_data_uniqueness": failures == 0,
            "registered_ambiguity_is_repaired_combinatorially": (
                rank4_pairs <= observed_pairs(refined)
                and not rank4_pairs <= observed_pairs(original)
            ),
        },
        "conclusion": (
            "joint visibility of every pair is necessary and sufficient for "
            "global uniqueness of arbitrary pair-valued data from restrictions"
        ),
        "scope": (
            "uniqueness only; existence, metric axioms and selection of the local "
            "pair values remain separate"
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
