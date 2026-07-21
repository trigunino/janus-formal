"""MF-INV-002: composition stability of intrinsically selected involutions."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

try:
    from scripts.audit_program_m_canonical_involution import (
        automorphisms,
        canonical_involutions,
        compose,
    )
except ModuleNotFoundError:
    from audit_program_m_canonical_involution import automorphisms, canonical_involutions, compose


def disjoint_union(left: int, right: int, piece_size: int = 2) -> int:
    total = 2 * piece_size
    mask = 0
    for source in range(piece_size):
        for target in range(piece_size):
            if left & (1 << (piece_size * source + target)):
                mask |= 1 << (total * source + target)
            if right & (1 << (piece_size * source + target)):
                mask |= 1 << (
                    total * (piece_size + source) + piece_size + target
                )
    return mask


def unique_nontrivial_central(mask: int, size: int):
    identity = tuple(range(size))
    nontrivial = tuple(
        p for p in canonical_involutions(mask, size) if p != identity
    )
    return nontrivial[0] if len(nontrivial) == 1 else None


def run_audit() -> dict[str, object]:
    piece_size = 2
    eligible = tuple(
        (mask, unique_nontrivial_central(mask, piece_size))
        for mask in range(1 << (piece_size * piece_size))
        if unique_nontrivial_central(mask, piece_size) is not None
    )
    rows = []
    identity4 = tuple(range(4))
    for left_mask, left_inv in eligible:
        for right_mask, right_inv in eligible:
            union = disjoint_union(left_mask, right_mask, piece_size)
            product_inv = (
                left_inv[0],
                left_inv[1],
                piece_size + right_inv[0],
                piece_size + right_inv[1],
            )
            symmetries = automorphisms(union, 4)
            central = canonical_involutions(union, 4)
            nontrivial_central = tuple(p for p in central if p != identity4)
            product_is_valid = (
                product_inv in symmetries
                and compose(product_inv, product_inv) == identity4
            )
            rows.append(
                {
                    "left_mask": left_mask,
                    "right_mask": right_mask,
                    "global_unique": len(nontrivial_central) == 1,
                    "componentwise_involution_is_valid": product_is_valid,
                    "global_nontrivial_central_count": len(nontrivial_central),
                }
            )
    failed_uniqueness = [row for row in rows if not row["global_unique"]]
    return {
        "program": "MF-INV-002",
        "protocol": {
            "piece_rank": piece_size,
            "eligible_labelled_relations": len(eligible),
            "ordered_compositions": len(rows),
        },
        "counts": {
            "compositions_retaining_unique_intrinsic_involution": sum(
                row["global_unique"] for row in rows
            ),
            "compositions_losing_uniqueness": len(failed_uniqueness),
            "componentwise_involution_valid": sum(
                row["componentwise_involution_is_valid"] for row in rows
            ),
        },
        "first_uniqueness_failure": failed_uniqueness[0] if failed_uniqueness else None,
        "gates": {
            "intrinsic_uniqueness_is_not_closed_under_composition": bool(failed_uniqueness),
            "supplied_componentwise_involution_always_composes": all(
                row["componentwise_involution_is_valid"] for row in rows
            ),
        },
        "conclusion": (
            "unique intrinsic involutions are not composition-stable, whereas "
            "relations equipped with chosen involutions compose componentwise"
        ),
        "scope": "exact disjoint compositions of all eligible labelled rank-two relations",
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
