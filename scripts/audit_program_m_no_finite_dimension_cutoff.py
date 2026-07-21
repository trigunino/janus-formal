"""MF-DIM-003: unbounded minimal obstructions to order dimension at most two."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.program_m_dimension_two import polynomial_two_order_realizer
except ModuleNotFoundError:
    from program_m_dimension_two import polynomial_two_order_realizer


PROTOCOL = {
    "protocol_id": "MF-DIM-003-v1",
    "crown_half_sizes": [3, 4, 5, 8, 12, 16, 24, 32],
}


def crown_order(half_size: int) -> np.ndarray:
    """Return the height-two crown C_2n (the incidence poset of a cycle)."""
    if half_size < 3:
        raise ValueError("a crown requires half_size >= 3")
    size = 2 * half_size
    order = np.eye(size, dtype=bool)
    for index in range(half_size):
        minimal = index
        order[minimal, half_size + index] = True
        order[minimal, half_size + ((index - 1) % half_size)] = True
    return order


def remove_point(order: np.ndarray, point: int) -> np.ndarray:
    keep = [index for index in range(len(order)) if index != point]
    return order[np.ix_(keep, keep)]


def run_audit() -> dict[str, object]:
    rows = []
    for half_size in PROTOCOL["crown_half_sizes"]:
        order = crown_order(half_size)
        whole_has_dimension_at_most_two = polynomial_two_order_realizer(order) is not None
        deletion_witnesses = [
            polynomial_two_order_realizer(remove_point(order, point))
            for point in range(len(order))
        ]
        rows.append(
            {
                "half_size": half_size,
                "points": len(order),
                "whole_has_dimension_at_most_two": whole_has_dimension_at_most_two,
                "all_one_point_deletions_have_dimension_at_most_two": all(
                    witness is not None for witness in deletion_witnesses
                ),
                "deletion_certificates": len(order),
            }
        )
    return {
        "program": "MF-DIM-003",
        "protocol": PROTOCOL,
        "rows": rows,
        "gates": {
            "every_crown_is_an_obstruction": all(
                not row["whole_has_dimension_at_most_two"] for row in rows
            ),
            "every_tested_crown_is_point_minimal": all(
                row["all_one_point_deletions_have_dimension_at_most_two"] for row in rows
            ),
            "obstructions_reach_rank_64": rows[-1]["points"] == 64,
        },
        "consequence": (
            "dimension at most two has no universal finite induced-subposet cutoff; "
            "an all-rank argument must use assumptions specific to the model"
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
