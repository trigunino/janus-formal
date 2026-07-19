"""MF-REP-004: finite orbit certificate for an exchangeable realizer lift."""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_induced_patterns import relation_mask
    from scripts.audit_program_m_two_order_representation import (
        linear_order_matrix,
        two_order_realizer_fast,
    )
except ModuleNotFoundError:
    from audit_program_m_induced_patterns import relation_mask
    from audit_program_m_two_order_representation import linear_order_matrix, two_order_realizer_fast


SIZE = 5


def relabel(matrix: np.ndarray, permutation: tuple[int, ...]) -> np.ndarray:
    indices = np.array(permutation)
    return matrix[np.ix_(indices, indices)]


def encoded_triple(
    poset: np.ndarray, first: np.ndarray, second: np.ndarray
) -> tuple[int, int, int]:
    return relation_mask(poset), relation_mask(first), relation_mask(second)


def orbit_lift() -> Counter[tuple[int, int, int]]:
    points = np.array([[0, 1], [1, 4], [2, 0], [3, 3], [4, 2]])
    poset = np.all(points[:, None, :] <= points[None, :, :], axis=2)
    realizer = two_order_realizer_fast(poset)
    assert realizer is not None
    first, second = map(linear_order_matrix, realizer)
    return Counter(
        encoded_triple(
            relabel(poset, permutation),
            relabel(first, permutation),
            relabel(second, permutation),
        )
        for permutation in itertools.permutations(range(SIZE))
    )


def decode(mask: int) -> np.ndarray:
    return np.array(
        [bool(mask & (1 << index)) for index in range(SIZE * SIZE)], dtype=bool
    ).reshape(SIZE, SIZE)


def act_on_distribution(
    distribution: Counter[tuple[int, int, int]], permutation: tuple[int, ...]
) -> Counter[tuple[int, int, int]]:
    acted: Counter[tuple[int, int, int]] = Counter()
    for triple, multiplicity in distribution.items():
        acted[
            encoded_triple(*(relabel(decode(mask), permutation) for mask in triple))
        ] += multiplicity
    return acted


def run_audit() -> dict[str, object]:
    lift = orbit_lift()
    marginal = Counter()
    intersections_hold = True
    for (poset_mask, first_mask, second_mask), multiplicity in lift.items():
        marginal[poset_mask] += multiplicity
        intersections_hold &= np.array_equal(
            decode(first_mask) & decode(second_mask), decode(poset_mask)
        )
    adjacent_transpositions = [
        tuple(list(range(index)) + [index + 1, index] + list(range(index + 2, SIZE)))
        for index in range(SIZE - 1)
    ]
    lift_invariant = all(
        act_on_distribution(lift, permutation) == lift
        for permutation in adjacent_transpositions
    )
    marginal_invariant = all(
        Counter(
            {
                relation_mask(relabel(decode(mask), permutation)): multiplicity
                for mask, multiplicity in marginal.items()
            }
        )
        == marginal
        for permutation in adjacent_transpositions
    )
    return {
        "program": "MF-REP-004",
        "finite_group": f"S_{SIZE}",
        "orbit_mass": sum(lift.values()),
        "distinct_joint_states": len(lift),
        "distinct_poset_states": len(marginal),
        "gates": {
            "every_joint_state_realizes_its_poset": bool(intersections_hold),
            "joint_lift_is_exchangeable": lift_invariant,
            "poset_marginal_is_exchangeable": marginal_invariant,
            "projection_preserves_total_mass": sum(lift.values()) == sum(marginal.values()),
        },
        "infinite_extension": (
            "for an exchangeable law supported on globally two-dimensional countable "
            "posets: take a Borel lift, average over S_n, use compactness for an "
            "invariant lift, and choose an extreme lift over an ergodic marginal"
        ),
        "scope": "finite executable analogue; the infinite proof uses standard Borel selection and compactness",
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
