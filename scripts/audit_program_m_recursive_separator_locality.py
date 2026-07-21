"""MF-SEP-001: intrinsic recursive separators and a crown countermodel."""

from __future__ import annotations

import argparse
from functools import lru_cache
import itertools
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_no_finite_dimension_cutoff import crown_order
    from scripts.program_m_dimension_two import polynomial_two_order_realizer
except ModuleNotFoundError:
    from audit_program_m_no_finite_dimension_cutoff import crown_order
    from program_m_dimension_two import polynomial_two_order_realizer


PROTOCOL = {
    "protocol_id": "MF-SEP-001-v1",
    "crown_half_sizes": [3, 4, 5, 8, 12, 16],
    "balance_fraction": 2 / 3,
    "separator_width": 2,
}


def cover_graph(order: np.ndarray) -> np.ndarray:
    """Undirected Hasse/cover graph computed from the order alone."""
    relation = np.asarray(order, dtype=bool)
    size = len(relation)
    strict = relation & ~np.eye(size, dtype=bool)
    covers = strict.copy()
    for left in range(size):
        for right in np.flatnonzero(strict[left]):
            intermediates = strict[left] & strict[:, right]
            if np.any(intermediates):
                covers[left, right] = False
    return covers | covers.T


def recursive_separator_certificate(
    adjacency: np.ndarray, max_width: int = 2
) -> dict[str, object] | None:
    """Find a recursive 2/3-balanced vertex-separator certificate."""
    graph = np.asarray(adjacency, dtype=bool)
    size = len(graph)

    def components(vertices: frozenset[int]) -> list[frozenset[int]]:
        remaining = set(vertices)
        result = []
        while remaining:
            root = remaining.pop()
            component = {root}
            stack = [root]
            while stack:
                point = stack.pop()
                neighbours = set(np.flatnonzero(graph[point])) & remaining
                remaining -= neighbours
                component |= neighbours
                stack.extend(neighbours)
            result.append(frozenset(component))
        return result

    @lru_cache(maxsize=None)
    def decompose(vertices: frozenset[int]) -> dict[str, object] | None:
        if len(vertices) <= 1:
            return {"vertices": sorted(vertices), "separator": [], "children": []}
        bound = int(float(PROTOCOL["balance_fraction"]) * len(vertices))
        ordered = sorted(vertices)
        for width in range(max_width + 1):
            for separator_tuple in itertools.combinations(ordered, width):
                separator = frozenset(separator_tuple)
                pieces = components(vertices - separator)
                if any(len(piece) > bound for piece in pieces):
                    continue
                children = [decompose(piece) for piece in pieces]
                if all(child is not None for child in children):
                    return {
                        "vertices": ordered,
                        "separator": list(separator_tuple),
                        "children": children,
                    }
        return None

    return decompose(frozenset(range(size)))


def run_audit() -> dict[str, object]:
    rows = []
    for half_size in PROTOCOL["crown_half_sizes"]:
        order = crown_order(half_size)
        certificate = recursive_separator_certificate(
            cover_graph(order), int(PROTOCOL["separator_width"])
        )
        rows.append(
            {
                "points": len(order),
                "recursive_separator_width_at_most_two": certificate is not None,
                "dimension_at_most_two": polynomial_two_order_realizer(order) is not None,
            }
        )
    return {
        "program": "MF-SEP-001",
        "protocol": PROTOCOL,
        "definition": (
            "the intrinsic cover graph recursively admits vertex separators of size "
            "at most two, leaving components of at most two thirds of the parent"
        ),
        "rows": rows,
        "gates": {
            "all_crowns_are_recursively_local": all(
                row["recursive_separator_width_at_most_two"] for row in rows
            ),
            "all_crowns_still_break_dimension_two": all(
                not row["dimension_at_most_two"] for row in rows
            ),
        },
        "conclusion": (
            "recursive balanced-separator locality is intrinsic and non-circular, "
            "but too weak to force two orders"
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
