"""MF-COMP-002: finite audit of configuration composition and cross-data ambiguity."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import numpy as np


def disjoint_sum(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    size_left, size_right = len(left), len(right)
    result = np.zeros((size_left + size_right, size_left + size_right), dtype=bool)
    result[:size_left, :size_left] = left
    result[size_left:, size_left:] = right
    return result


def relabel(relation: np.ndarray, permutation: tuple[int, ...]) -> np.ndarray:
    return relation[np.ix_(permutation, permutation)]


def two_piece_composites(left_loop: bool, right_loop: bool) -> list[np.ndarray]:
    composites = []
    for left_to_right, right_to_left in itertools.product((False, True), repeat=2):
        composites.append(
            np.array(
                [[left_loop, left_to_right], [right_to_left, right_loop]], dtype=bool
            )
        )
    return composites


def run_audit() -> dict[str, object]:
    left = np.array([[True, True], [False, False]], dtype=bool)
    middle = np.array([[False]], dtype=bool)
    right = np.array([[True, False], [True, True]], dtype=bool)
    associative = np.array_equal(
        disjoint_sum(disjoint_sum(left, middle), right),
        disjoint_sum(left, disjoint_sum(middle, right)),
    )
    swapped = disjoint_sum(right, left)
    block_swap = tuple(range(len(right), len(right) + len(left))) + tuple(range(len(right)))
    commutative_up_to_relabelling = np.array_equal(
        relabel(swapped, block_swap), disjoint_sum(left, right)
    )
    empty = np.zeros((0, 0), dtype=bool)
    composites = two_piece_composites(False, False)
    return {
        "program": "MF-COMP-002",
        "finite_example": {
            "cross_composites_with_identical_one_point_pieces": len(composites),
            "cross_edge_counts": sorted(int(np.count_nonzero(item)) for item in composites),
        },
        "gates": {
            "disjoint_sum_is_associative": associative,
            "disjoint_sum_is_commutative_up_to_relabelling": commutative_up_to_relabelling,
            "empty_configuration_is_left_unit": np.array_equal(disjoint_sum(empty, left), left),
            "empty_configuration_is_right_unit": np.array_equal(disjoint_sum(left, empty), left),
            "pieces_do_not_determine_cross_relations": len({item.tobytes() for item in composites}) == 4,
        },
        "conclusion": (
            "disjoint composition is canonical; interacting gluing requires explicit "
            "cross-relation/interface data"
        ),
        "scope": "pure relational composition; no geometry, dynamics or physical interaction",
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
