"""MF-GLUE-002: finite local-to-global coherence audit for relational gluings."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import numpy as np


Vertex = tuple[int, int]


def _validate_interfaces(
    pieces: list[np.ndarray], interfaces: list[tuple[Vertex, ...]]
) -> None:
    for interface in interfaces:
        if len(set(interface)) != len(interface):
            raise ValueError("an interface repeats a vertex")
        if len({piece for piece, _ in interface}) != len(interface):
            raise ValueError("one interface cannot use two vertices from the same piece")
        for piece, vertex in interface:
            if piece >= len(pieces) or vertex >= len(pieces[piece]):
                raise ValueError("interface vertex is out of range")

    # Whenever two interface classes are both represented in several pieces,
    # every such piece must induce the same relation between them.
    for first, second in itertools.product(interfaces, repeat=2):
        first_by_piece = dict(first)
        second_by_piece = dict(second)
        common = sorted(set(first_by_piece) & set(second_by_piece))
        values = {
            bool(pieces[piece][first_by_piece[piece], second_by_piece[piece]])
            for piece in common
        }
        if len(values) > 1:
            raise ValueError("pieces disagree on an interface relation")


def glue_diagram(
    pieces: list[np.ndarray],
    interfaces: list[tuple[Vertex, ...]],
    interface_order: tuple[int, ...] | None = None,
) -> np.ndarray:
    _validate_interfaces(pieces, interfaces)
    vertices = [(piece, point) for piece, relation in enumerate(pieces) for point in range(len(relation))]
    parent = {vertex: vertex for vertex in vertices}

    def find(vertex: Vertex) -> Vertex:
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    def union(left: Vertex, right: Vertex) -> None:
        root_left, root_right = find(left), find(right)
        if root_left != root_right:
            low, high = sorted((root_left, root_right))
            parent[high] = low

    order = interface_order or tuple(range(len(interfaces)))
    for index in order:
        interface = interfaces[index]
        for vertex in interface[1:]:
            union(interface[0], vertex)

    roots = sorted({find(vertex) for vertex in vertices})
    root_index = {root: index for index, root in enumerate(roots)}
    result = np.zeros((len(roots), len(roots)), dtype=bool)
    for piece, relation in enumerate(pieces):
        for source, target in np.argwhere(relation):
            result[root_index[find((piece, int(source)))], root_index[find((piece, int(target)))]] = True
    return result


def canonical_relation(relation: np.ndarray) -> bytes:
    return min(
        relation[np.ix_(permutation, permutation)].tobytes()
        for permutation in itertools.permutations(range(len(relation)))
    )


def run_audit() -> dict[str, object]:
    edge = np.array([[False, True], [False, False]], dtype=bool)
    pieces = [edge.copy(), edge.copy(), edge.copy()]
    interfaces = [((0, 1), (1, 0)), ((1, 1), (2, 0)), ((2, 1), (0, 0))]
    outputs = [
        glue_diagram(pieces, interfaces, order)
        for order in itertools.permutations(range(len(interfaces)))
    ]
    order_independent = len({output.tobytes() for output in outputs}) == 1

    renamed_pieces = [piece[::-1, ::-1] for piece in reversed(pieces)]
    renamed_interfaces = [
        tuple((2 - piece, 1 - vertex) for piece, vertex in interface)
        for interface in reversed(interfaces)
    ]
    renamed_output = glue_diagram(renamed_pieces, renamed_interfaces)
    renaming_invariant = canonical_relation(outputs[0]) == canonical_relation(renamed_output)

    incompatible = [edge.copy(), np.zeros((2, 2), dtype=bool)]
    incompatible_interfaces = [((0, 0), (1, 0)), ((0, 1), (1, 1))]
    incompatibility_rejected = False
    try:
        glue_diagram(incompatible, incompatible_interfaces)
    except ValueError:
        incompatibility_rejected = True

    chain_interfaces = [((0, 1), (1, 0)), ((1, 1), (2, 0))]
    free_chain = glue_diagram(pieces, chain_interfaces)
    enriched_chain = free_chain.copy()
    enriched_chain[0, -1] = True
    local_data_do_not_fix_arbitrary_global = bool(
        not np.array_equal(free_chain, enriched_chain)
        and not free_chain[0, -1]
        and enriched_chain[0, -1]
    )

    return {
        "program": "MF-GLUE-002",
        "protocol": {
            "pieces": 3,
            "interfaces": 3,
            "interface_orders": len(outputs),
        },
        "result": {
            "global_points": len(outputs[0]),
            "global_relations": int(np.count_nonzero(outputs[0])),
        },
        "gates": {
            "all_interface_orders_give_same_global_relation": order_independent,
            "renaming_gives_isomorphic_global_relation": renaming_invariant,
            "incompatible_overlap_is_rejected": incompatibility_rejected,
            "free_gluing_adds_no_extra_relations": int(np.count_nonzero(outputs[0])) == 3,
            "local_data_do_not_determine_arbitrary_global":
                local_data_do_not_fix_arbitrary_global,
        },
        "scope": (
            "exhaustive finite coherence audit for the declared diagram; general "
            "relational colimit coherence is not yet formalized in Lean"
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
