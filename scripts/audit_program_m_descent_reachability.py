"""MF-DESC-002: audit global closure against chains of local primitive steps."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_primitive_descent import reflexive_transitive_closure
except ModuleNotFoundError:
    from audit_program_m_primitive_descent import reflexive_transitive_closure


PROTOCOL = {
    "protocol_id": "MF-DESC-002-v1",
    "seed": 2026071823,
    "random_diagrams": 4096,
    "maximum_points": 10,
}


def chain_reachability(size: int, local_edges: list[tuple[int, int]]) -> np.ndarray:
    adjacency = [[] for _ in range(size)]
    for source, target in local_edges:
        adjacency[source].append(target)
    result = np.eye(size, dtype=bool)
    for source in range(size):
        seen = {source}
        stack = [source]
        while stack:
            point = stack.pop()
            for target in adjacency[point]:
                if target not in seen:
                    seen.add(target)
                    stack.append(target)
        result[source, list(seen)] = True
    return result


def run_audit() -> dict[str, object]:
    rng = np.random.default_rng(int(PROTOCOL["seed"]))
    disagreements = 0
    for _ in range(int(PROTOCOL["random_diagrams"])):
        size = int(rng.integers(1, int(PROTOCOL["maximum_points"]) + 1))
        patch_count = int(rng.integers(1, 6))
        primitive_global = np.zeros((size, size), dtype=bool)
        local_edges = []
        for _ in range(patch_count):
            patch_size = int(rng.integers(1, size + 1))
            vertices = np.sort(rng.choice(size, size=patch_size, replace=False))
            local = rng.random((patch_size, patch_size)) < 0.2
            for left, right in np.argwhere(local):
                source, target = int(vertices[left]), int(vertices[right])
                primitive_global[source, target] = True
                local_edges.append((source, target))
        closure_method = reflexive_transitive_closure(primitive_global)
        chain_method = chain_reachability(size, local_edges)
        if not np.array_equal(closure_method, chain_method):
            disagreements += 1

    first_patch = np.array([[False, True], [False, False]], dtype=bool)
    second_patch = first_patch.copy()
    patchwise_union = np.eye(3, dtype=bool)
    patchwise_union[np.ix_((0, 1), (0, 1))] |= reflexive_transitive_closure(first_patch)
    patchwise_union[np.ix_((1, 2), (1, 2))] |= reflexive_transitive_closure(second_patch)
    primitive_union = np.zeros((3, 3), dtype=bool)
    primitive_union[0, 1] = primitive_union[1, 2] = True
    global_closure = reflexive_transitive_closure(primitive_union)

    return {
        "program": "MF-DESC-002",
        "protocol": PROTOCOL,
        "random_disagreements": disagreements,
        "three_point_example": {
            "patchwise_closure_sees_0_to_2": bool(patchwise_union[0, 2]),
            "global_closure_sees_0_to_2": bool(global_closure[0, 2]),
        },
        "gates": {
            "global_closure_equals_local_step_chains": disagreements == 0,
            "patchwise_closure_then_union_is_insufficient":
                not bool(patchwise_union[0, 2]) and bool(global_closure[0, 2]),
        },
        "conclusion": (
            "glue primitive relations first and close globally; closing patches "
            "separately before union misses chains crossing interfaces"
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
