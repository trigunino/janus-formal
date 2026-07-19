"""MF-DIST-001: unit-cost shortest paths as canonical directed pair data."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


def shortest_distances(mask: int, size: int) -> tuple[tuple[float, ...], ...]:
    distance = [[math.inf] * size for _ in range(size)]
    for vertex in range(size):
        distance[vertex][vertex] = 0
    for source in range(size):
        for target in range(size):
            if mask & (1 << (size * source + target)):
                distance[source][target] = min(distance[source][target], 1)
    for middle in range(size):
        for source in range(size):
            for target in range(size):
                distance[source][target] = min(
                    distance[source][target],
                    distance[source][middle] + distance[middle][target],
                )
    return tuple(tuple(row) for row in distance)


def triangle_holds(distance: tuple[tuple[float, ...], ...]) -> bool:
    size = len(distance)
    return all(
        distance[x][z] <= distance[x][y] + distance[y][z]
        for x in range(size)
        for y in range(size)
        for z in range(size)
    )


def relabel(mask: int, size: int, permutation: tuple[int, ...]) -> int:
    return sum(
        1 << (size * permutation[source] + permutation[target])
        for source in range(size)
        for target in range(size)
        if mask & (1 << (size * source + target))
    )


def relabel_invariant(mask: int, size: int, permutation: tuple[int, ...]) -> bool:
    before = shortest_distances(mask, size)
    after = shortest_distances(relabel(mask, size, permutation), size)
    return all(
        before[x][y] == after[permutation[x]][permutation[y]]
        for x in range(size)
        for y in range(size)
    )


def run_audit() -> dict[str, object]:
    size = 4
    failures = 0
    permutation = tuple(reversed(range(size)))
    for mask in range(1 << (size * size)):
        distance = shortest_distances(mask, size)
        if not triangle_holds(distance) or not relabel_invariant(mask, size, permutation):
            failures += 1

    witness_mask = 1 << 1
    witness = shortest_distances(witness_mask, size)
    return {
        "program": "MF-DIST-001",
        "protocol": {
            "rank": size,
            "relations": 1 << (size * size),
            "primitive_edge_cost": 1,
            "unreachable_cost": "infinity",
        },
        "failures": failures,
        "gates": {
            "all_directed_triangle_inequalities_hold": failures == 0,
            "all_reversal_relabellings_are_equivariant": failures == 0,
        },
        "mf_geo_001_witness": {
            "distance_0_to_1": witness[0][1],
            "distance_1_to_0": "infinity" if math.isinf(witness[1][0]) else witness[1][0],
            "distance_2_to_3": "infinity" if math.isinf(witness[2][3]) else witness[2][3],
        },
        "conclusion": (
            "unit primitive costs canonically generate an invariant extended "
            "directed shortest-path distance"
        ),
        "scope": (
            "generalized directed geometry only; unit cost is explicit and the "
            "construction does not select a Lorentzian metric"
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
