"""MF-GLUE-001: finite audit of free relational gluing along an interface."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np


def glue_relations(
    left: np.ndarray,
    right: np.ndarray,
    left_interface: tuple[int, ...],
    right_interface: tuple[int, ...],
) -> np.ndarray:
    if len(left_interface) != len(right_interface):
        raise ValueError("interface maps must have the same domain")
    if len(set(left_interface)) != len(left_interface) or len(set(right_interface)) != len(right_interface):
        raise ValueError("interface maps must be injective")
    left_trace = left[np.ix_(left_interface, left_interface)]
    right_trace = right[np.ix_(right_interface, right_interface)]
    if not np.array_equal(left_trace, right_trace):
        raise ValueError("the two pieces disagree on the induced interface relation")

    right_to_output = {}
    next_index = len(left)
    interface_lookup = dict(zip(right_interface, left_interface, strict=True))
    for point in range(len(right)):
        if point in interface_lookup:
            right_to_output[point] = interface_lookup[point]
        else:
            right_to_output[point] = next_index
            next_index += 1
    result = np.zeros((next_index, next_index), dtype=bool)
    result[: len(left), : len(left)] |= left
    for source in range(len(right)):
        for target in range(len(right)):
            if right[source, target]:
                result[right_to_output[source], right_to_output[target]] = True
    return result


def run_audit() -> dict[str, object]:
    left = np.array([[False, True], [False, False]], dtype=bool)
    right = np.array([[False, False], [True, False]], dtype=bool)
    glued = glue_relations(left, right, (0,), (0,))
    incompatible = right.copy()
    incompatible[0, 0] = True
    incompatibility_rejected = False
    try:
        glue_relations(left, incompatible, (0,), (0,))
    except ValueError:
        incompatibility_rejected = True
    return {
        "program": "MF-GLUE-001",
        "finite_example": {
            "left_points": 2,
            "right_points": 2,
            "interface_points": 1,
            "pushout_points": len(glued),
            "inherited_relations": int(np.count_nonzero(glued)),
        },
        "gates": {
            "interface_is_identified_once": len(glued) == 3,
            "left_relation_is_preserved": bool(glued[0, 1]),
            "right_relation_is_preserved": bool(glued[2, 0]),
            "no_new_cross_relation_is_invented": not bool(glued[2, 1]),
            "incompatible_interface_is_rejected": incompatibility_rejected,
        },
        "conclusion": (
            "free gluing is canonical after compatible interface embeddings are "
            "supplied; the interface is extra input and no cross relation is invented"
        ),
        "scope": "primitive relations before any optional transitive closure",
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
