"""MF-INV-003: exhaustive carrier audit for equivariant interface gluing."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


Vertex = tuple[int, int]


def partial_bijections() -> tuple[tuple[tuple[int, int], ...], ...]:
    interfaces = [()]
    interfaces.extend(((left, right),) for left in range(2) for right in range(2))
    interfaces.extend(tuple(zip((0, 1), permutation)) for permutation in itertools.permutations((0, 1)))
    return tuple(interfaces)


def quotient_classes(interface: tuple[tuple[int, int], ...]) -> dict[Vertex, Vertex]:
    vertices = tuple((piece, point) for piece in range(2) for point in range(2))
    parent = {vertex: vertex for vertex in vertices}

    def find(vertex: Vertex) -> Vertex:
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    def union(left: Vertex, right: Vertex) -> None:
        a, b = find(left), find(right)
        if a != b:
            parent[max(a, b)] = min(a, b)

    for left, right in interface:
        union((0, left), (1, right))
    return {vertex: find(vertex) for vertex in vertices}


def respects_quotient(
    left_inv: tuple[int, int],
    right_inv: tuple[int, int],
    classes: dict[Vertex, Vertex],
) -> bool:
    sigma = {
        (0, point): (0, left_inv[point]) for point in range(2)
    } | {
        (1, point): (1, right_inv[point]) for point in range(2)
    }
    return all(
        classes[x] != classes[y] or classes[sigma[x]] == classes[sigma[y]]
        for x in classes
        for y in classes
    )


def run_audit() -> dict[str, object]:
    involutions = ((0, 1), (1, 0))
    interfaces = partial_bijections()
    rows = []
    for left_inv, right_inv, interface in itertools.product(
        involutions, involutions, interfaces
    ):
        classes = quotient_classes(interface)
        compatible = respects_quotient(left_inv, right_inv, classes)
        rows.append(
            {
                "left_involution": list(left_inv),
                "right_involution": list(right_inv),
                "interface": [list(pair) for pair in interface],
                "descends": compatible,
            }
        )
    incompatible = next(
        row
        for row in rows
        if row["left_involution"] == [1, 0]
        and row["right_involution"] == [1, 0]
        and row["interface"] == [[0, 0]]
    )
    compatible_full = next(
        row
        for row in rows
        if row["left_involution"] == [1, 0]
        and row["right_involution"] == [1, 0]
        and row["interface"] == [[0, 0], [1, 1]]
    )
    return {
        "program": "MF-INV-003",
        "protocol": {
            "piece_involution_pairs": len(involutions) ** 2,
            "partial_interfaces": len(interfaces),
            "cases": len(rows),
        },
        "counts": {
            "equivariant_descents": sum(row["descends"] for row in rows),
            "rejected_interfaces": sum(not row["descends"] for row in rows),
        },
        "witnesses": {
            "single_unpaired_identification": incompatible,
            "full_paired_identification": compatible_full,
        },
        "gates": {
            "single_unpaired_identification_is_rejected": not incompatible["descends"],
            "full_paired_identification_descends": compatible_full["descends"],
            "both_compatible_and_incompatible_cases_exist": (
                any(row["descends"] for row in rows)
                and any(not row["descends"] for row in rows)
            ),
        },
        "conclusion": (
            "a chosen involution descends through gluing exactly when the generated "
            "identifications are preserved by the componentwise involution"
        ),
        "scope": "general Lean quotient theorem plus exhaustive two-by-two carrier audit",
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
