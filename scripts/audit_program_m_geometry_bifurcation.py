"""MF-GEO-001: bridge primitive relations to non-unique metric realizations."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

try:
    from scripts.audit_program_m_free_preorder import (
        reflexive_transitive_closure,
        relation_from_mask,
    )
    from scripts.audit_program_m_embedding_ambiguity import (
        interval_square_signature,
        product_order_realizers,
    )
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_free_preorder import (
        reflexive_transitive_closure,
        relation_from_mask,
    )
    from audit_program_m_embedding_ambiguity import (
        interval_square_signature,
        product_order_realizers,
    )


def matrix_mask(relation) -> int:
    size = relation.shape[0]
    return sum(
        1 << (size * source + target)
        for source in range(size)
        for target in range(size)
        if relation[source, target]
    )


def run_audit() -> dict[str, object]:
    size = 4
    primitive_mask = 1 << 1  # One primitive arrow 0 -> 1; 2 and 3 are isolated.
    free_preorder = reflexive_transitive_closure(
        relation_from_mask(primitive_mask, size)
    )
    preorder_mask = matrix_mask(free_preorder)
    expected_mask = primitive_mask | sum(
        1 << (size * vertex + vertex) for vertex in range(size)
    )
    realizers = product_order_realizers(preorder_mask, size)
    signatures = sorted(
        {
            interval_square_signature(coordinates, preorder_mask, size)
            for coordinates in realizers
        }
    )
    return {
        "program": "MF-GEO-001",
        "input": {
            "objects": size,
            "primitive_strict_pairs": [[0, 1]],
            "assumed_geometry": False,
        },
        "free_preorder": {
            "strict_pairs": [[0, 1]],
            "matches_expected_closure": preorder_mask == expected_mask,
        },
        "candidate_reconstruction": {
            "external_conventions": [
                "two linear-extension ranks are null coordinates",
                "uniform rank spacing",
                "ds^2=-du*dv",
            ],
            "realizers": len(realizers),
            "inequivalent_metric_classes": len(signatures),
            "metric_signatures": signatures,
        },
        "gates": {
            "primitive_to_free_preorder_bridge": preorder_mask == expected_mask,
            "same_preorder_has_multiple_metric_classes": len(signatures) > 1,
        },
        "conclusion": (
            "the free preorder produced by Program M does not by itself select "
            "a unique metric geometry"
        ),
        "missing_information": (
            "a reconstruction or selection principle beyond primitive relations "
            "and their free preorder"
        ),
        "scope": (
            "finite counterexample for the declared rank-coordinate reconstruction; "
            "not a no-go for probabilistic or continuum reconstruction"
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
