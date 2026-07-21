"""MF-FREE-001: exhaustive rank-three audit of the free-preorder property."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_primitive_descent import reflexive_transitive_closure
except ModuleNotFoundError:
    from audit_program_m_primitive_descent import reflexive_transitive_closure


def relation_from_mask(mask: int, size: int) -> np.ndarray:
    return np.array(
        [[bool(mask & (1 << (size * left + right))) for right in range(size)]
         for left in range(size)],
        dtype=bool,
    )


def is_preorder(relation: np.ndarray) -> bool:
    reflexive = bool(np.all(np.diag(relation)))
    transitive = bool(np.all((relation.astype(int) @ relation.astype(int) == 0) | relation))
    return reflexive and transitive


def run_audit() -> dict[str, object]:
    size = 3
    relations = [relation_from_mask(mask, size) for mask in range(1 << (size * size))]
    preorders = [relation for relation in relations if is_preorder(relation)]
    failures = 0
    for primitive in relations:
        closure = reflexive_transitive_closure(primitive)
        if not is_preorder(closure) or not np.all(~primitive | closure):
            failures += 1
            continue
        for candidate in preorders:
            if np.all(~primitive | candidate) and not np.all(~closure | candidate):
                failures += 1
                break
    return {
        "program": "MF-FREE-001",
        "protocol": {
            "rank": size,
            "primitive_relations": len(relations),
            "candidate_preorders": len(preorders),
        },
        "failures": failures,
        "gates": {
            "every_closure_is_a_preorder": failures == 0,
            "every_closure_is_minimal": failures == 0,
        },
        "conclusion": (
            "reachability adds exactly reflexivity and transitivity: it is the "
            "least preorder containing the primitive relation"
        ),
        "scope": "free preorder only; no antisymmetry, topology, metric or geometry",
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
