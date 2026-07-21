"""MF-AX-001: classify proposed axioms around the dimension-two boundary."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_no_finite_dimension_cutoff import crown_order
    from scripts.audit_program_m_weak_kernel_axioms import product_order
    from scripts.program_m_dimension_two import polynomial_two_order_realizer
except ModuleNotFoundError:
    from audit_program_m_no_finite_dimension_cutoff import crown_order
    from audit_program_m_weak_kernel_axioms import product_order
    from program_m_dimension_two import polynomial_two_order_realizer


PROTOCOL = {"protocol_id": "MF-AX-001-v1", "seed": 2026071821, "rank": 16}


def run_audit() -> dict[str, object]:
    rng = np.random.default_rng(int(PROTOCOL["seed"]))
    product_3d = product_order(rng.random((int(PROTOCOL["rank"]), 3)))
    crown = crown_order(8)
    product_3d_breaks_two_orders = polynomial_two_order_realizer(product_3d) is None
    crown_breaks_two_orders = polynomial_two_order_realizer(crown) is None

    rows = [
        {
            "axiom": "partial_order_exchangeability_projectivity",
            "class": "too_weak",
            "reason": "iid three-dimensional product-order countermodel",
            "executable_witness": product_3d_breaks_two_orders,
        },
        {
            "axiom": "iid_atomless_continuous_symmetric_factorization",
            "class": "too_weak",
            "reason": "the same three-dimensional product model has all properties",
            "executable_witness": product_3d_breaks_two_orders,
        },
        {
            "axiom": "planar_or_low_treewidth_cover_structure",
            "class": "too_weak",
            "reason": "a crown has a cycle cover graph but order dimension three",
            "executable_witness": crown_breaks_two_orders,
        },
        {
            "axiom": "two_reversible_families_of_critical_pairs",
            "class": "circular",
            "reason": "critical-pair realizer characterization",
            "executable_witness": None,
        },
        {
            "axiom": "transitively_orientable_incomparability_graph",
            "class": "circular",
            "reason": "Dushnik--Miller characterization of dimension at most two",
            "executable_witness": None,
        },
        {
            "axiom": "boolean_dimension_at_most_two",
            "class": "circular",
            "reason": "Boolean and classical dimension coincide at value two",
            "executable_witness": None,
        },
        {
            "axiom": "recursive_intrinsic_separator_locality",
            "class": "too_weak",
            "reason": "MF-SEP-001 crown countermodel with recursive separator width two",
            "executable_witness": crown_breaks_two_orders,
        },
    ]
    return {
        "program": "MF-AX-001",
        "protocol": PROTOCOL,
        "rows": rows,
        "counts": {
            category: sum(row["class"] == category for row in rows)
            for category in ("too_weak", "circular", "open_not_yet_admissible")
        },
        "gates": {
            "all_axioms_classified": all(row["class"] for row in rows),
            "weak_classes_have_counterexamples": all(
                row["executable_witness"] is True
                for row in rows if row["class"] == "too_weak"
            ),
            "no_candidate_is_promoted_without_evidence": not any(
                row["class"] == "candidate" for row in rows
            ),
        },
        "next_step": (
            "define oriented gluing across separators without introducing two global "
            "orders, then falsify it with crowns and product orders"
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
