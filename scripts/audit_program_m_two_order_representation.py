"""MF-REP-001: exact finite audit of two-linear-order realizability."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import numpy as np


def is_partial_order(order: np.ndarray) -> bool:
    n = len(order)
    return (
        np.all(np.diag(order))
        and np.all(~(order & order.T) | np.eye(n, dtype=bool))
        and np.all((order.astype(int) @ order.astype(int) == 0) | order)
    )


def linear_extensions(order: np.ndarray) -> list[tuple[int, ...]]:
    return [
        permutation
        for permutation in itertools.permutations(range(len(order)))
        if all(
            permutation.index(left) < permutation.index(right)
            for left in range(len(order))
            for right in range(len(order))
            if left != right and order[left, right]
        )
    ]


def linear_order_matrix(permutation: tuple[int, ...]) -> np.ndarray:
    position = np.empty(len(permutation), dtype=int)
    position[list(permutation)] = np.arange(len(permutation))
    return position[:, None] <= position[None, :]


def iter_linear_extensions(order: np.ndarray):
    """Generate extensions by repeatedly selecting a currently minimal point."""
    size = len(order)
    strict = order.copy()
    np.fill_diagonal(strict, False)

    def visit(prefix: tuple[int, ...], remaining: frozenset[int]):
        if not remaining:
            yield prefix
            return
        minima = [
            point
            for point in sorted(remaining)
            if not any(strict[other, point] for other in remaining)
        ]
        for point in minima:
            yield from visit(prefix + (point,), remaining - {point})

    yield from visit((), frozenset(range(size)))


def two_order_realizer_fast(
    order: np.ndarray,
) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
    """Find a realizer by reversing every incomparable pair in one extension."""
    size = len(order)
    for first in iter_linear_extensions(order):
        position = np.empty(size, dtype=int)
        position[list(first)] = np.arange(size)
        second_relation = np.eye(size, dtype=bool)
        for left in range(size):
            for right in range(left + 1, size):
                if order[left, right]:
                    second_relation[left, right] = True
                elif order[right, left]:
                    second_relation[right, left] = True
                elif position[left] < position[right]:
                    second_relation[right, left] = True
                else:
                    second_relation[left, right] = True
        if np.all(
            (second_relation.astype(int) @ second_relation.astype(int) == 0)
            | second_relation
        ):
            predecessor_count = np.count_nonzero(second_relation, axis=0) - 1
            second = tuple(np.argsort(predecessor_count).tolist())
            return first, second
    return None


def two_order_realizer(order: np.ndarray) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
    extensions = linear_extensions(order)
    matrices = [linear_order_matrix(extension) for extension in extensions]
    for first_index, first in enumerate(matrices):
        for second_index in range(first_index, len(matrices)):
            if np.array_equal(first & matrices[second_index], order):
                return extensions[first_index], extensions[second_index]
    return None


def naturally_labelled_posets(size: int):
    pairs = list(itertools.combinations(range(size), 2))
    for mask in range(1 << len(pairs)):
        order = np.eye(size, dtype=bool)
        for index, (left, right) in enumerate(pairs):
            if mask & (1 << index):
                order[left, right] = True
        if is_partial_order(order):
            yield order


def standard_example_s3() -> np.ndarray:
    """Minimal elements a_i precede b_j exactly when i != j."""
    order = np.eye(6, dtype=bool)
    for i in range(3):
        for j in range(3):
            if i != j:
                order[i, 3 + j] = True
    return order


def run_audit() -> dict[str, object]:
    exhaustive = []
    for size in range(1, 6):
        count = 0
        failures = 0
        for order in naturally_labelled_posets(size):
            count += 1
            failures += int(two_order_realizer(order) is None)
        exhaustive.append(
            {"size": size, "naturally_labelled_posets": count, "without_two_order_realizer": failures}
        )
    s3 = standard_example_s3()
    s3_extensions = linear_extensions(s3)
    s3_realizer = two_order_realizer(s3)
    return {
        "program": "MF-REP-001",
        "definition": "Dushnik--Miller dimension at most two",
        "exhaustive_through_five": exhaustive,
        "six_point_obstruction": {
            "name": "standard example S3",
            "linear_extension_count": len(s3_extensions),
            "has_two_order_realizer": s3_realizer is not None,
            "relation_matrix": s3.astype(int).tolist(),
        },
        "gates": {
            "all_posets_through_five_have_dimension_at_most_two": all(
                row["without_two_order_realizer"] == 0 for row in exhaustive
            ),
            "standard_s3_is_a_partial_order": bool(is_partial_order(s3)),
            "standard_s3_has_no_two_order_realizer": s3_realizer is None,
        },
        "conclusion": (
            "rank four cannot establish a hidden two-coordinate representation; "
            "the first finite obstruction requires six observed objects"
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
