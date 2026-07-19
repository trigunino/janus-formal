"""MF-ADV-003: repeated two-level branches evade the exact-twin repair."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_adversarial_orders import DEFAULT_LINK_REFERENCE
    from scripts.audit_program_m_blind_dimension import order_matrix_from_null_points
    from scripts.audit_program_m_exact_twins import largest_twin_class
    from scripts.audit_program_m_intrinsic_link_fluctuations import intrinsic_link_fluctuation
    from scripts.evaluate_program_m_order_candidate import (
        DEFAULT_DIMENSION_REFERENCE,
        DEFAULT_LOCALITY_REFERENCE,
        evaluate_order,
    )
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_adversarial_orders import DEFAULT_LINK_REFERENCE
    from audit_program_m_blind_dimension import order_matrix_from_null_points
    from audit_program_m_exact_twins import largest_twin_class
    from audit_program_m_intrinsic_link_fluctuations import intrinsic_link_fluctuation
    from evaluate_program_m_order_candidate import (
        DEFAULT_DIMENSION_REFERENCE,
        DEFAULT_LOCALITY_REFERENCE,
        evaluate_order,
    )


DEFAULT_TWIN_REFERENCE = Path("outputs/program_m/mf_man_016_exact_twins.json")

PROTOCOL = {
    "protocol_id": "MF-ADV-003-v1",
    "cardinality": 256,
    "base_seed": 2026102800,
    "branch_multiplicities": [2, 3, 4, 6, 8, 10],
    "fresh_validation_replicates": 40,
    "pilot_seeds_excluded": True,
}


def repeated_two_level_branches(multiplicity: int, seed: int) -> np.ndarray:
    final_size = int(PROTOCOL["cardinality"])
    base_size = final_size - 2 * multiplicity + 1
    points = np.random.default_rng(seed).random((base_size, 2))
    base = order_matrix_from_null_points(points)
    del points
    order = np.zeros((final_size, final_size), dtype=bool)
    order[: 2 * multiplicity, : 2 * multiplicity] = np.eye(
        2 * multiplicity, dtype=bool
    )
    for branch in range(multiplicity):
        order[2 * branch, 2 * branch + 1] = True
    order[2 * multiplicity :, 2 * multiplicity :] = base[1:, 1:]
    for base_vertex in range(1, base_size):
        output_vertex = 2 * multiplicity + base_vertex - 1
        for branch in range(multiplicity):
            lower, upper = 2 * branch, 2 * branch + 1
            if base[0, base_vertex]:
                order[lower, output_vertex] = True
                order[upper, output_vertex] = True
            if base[base_vertex, 0]:
                order[output_vertex, lower] = True
                order[output_vertex, upper] = True
    return order


def _load(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def branch_adversary_audit() -> dict[str, object]:
    link_reference = _load(DEFAULT_LINK_REFERENCE)
    twin_reference = _load(DEFAULT_TWIN_REFERENCE)
    locality = _load(DEFAULT_LOCALITY_REFERENCE)
    dimension = _load(DEFAULT_DIMENSION_REFERENCE)
    size = int(PROTOCOL["cardinality"])
    link_row = next(row for row in link_reference["rows"] if row["cardinality"] == size)
    twin_row = next(row for row in twin_reference["rows"] if row["cardinality"] == size)
    link_lower, link_upper = link_row["acceptance_interval"]
    twin_threshold = twin_row["upper_threshold"]
    rows = []
    first_collision = None
    largest_passing_branch_family = 0
    for multiplicity in PROTOCOL["branch_multiplicities"]:
        passed = 0
        for replicate in range(int(PROTOCOL["fresh_validation_replicates"])):
            seed = int(PROTOCOL["base_seed"]) + 1_000 * multiplicity + replicate
            order = repeated_two_level_branches(multiplicity, seed)
            link_score = intrinsic_link_fluctuation(order)
            twin_score = largest_twin_class(order)
            report = evaluate_order(
                order,
                locality_reference=locality,
                dimension_reference=dimension,
                source_name=f"two_level_branches:{multiplicity}:seed={seed}",
            )
            all_four = (
                link_lower <= link_score <= link_upper
                and twin_score <= twin_threshold
                and report["status"] == "compatible_with_external_minkowski2_diagnostics"
            )
            passed += int(all_four)
            if all_four:
                largest_passing_branch_family = max(
                    largest_passing_branch_family, multiplicity
                )
                if first_collision is None:
                    first_collision = {
                        "branch_multiplicity": multiplicity,
                        "seed": seed,
                        "order_sha256": report["order_sha256"],
                        "link_score": link_score,
                        "largest_exact_twin_class": twin_score,
                        "dimension": report["diagnostics"]["myrheim_meyer_dimension"],
                        "locality": report["diagnostics"]["interval_abundance"],
                    }
        rows.append(
            {
                "branch_multiplicity": multiplicity,
                "generated": int(PROTOCOL["fresh_validation_replicates"]),
                "all_four_gates_accepted": passed,
            }
        )
    return {
        "program": "MF-ADV-003",
        "protocol": PROTOCOL,
        "construction": (
            "replace one element by repeated private two-element chains; branches "
            "are isomorphic but no branch vertices are exact past/future twins"
        ),
        "references": {
            "link_sha256": _sha256(DEFAULT_LINK_REFERENCE),
            "twin_sha256": _sha256(DEFAULT_TWIN_REFERENCE),
            "locality_sha256": _sha256(DEFAULT_LOCALITY_REFERENCE),
            "dimension_sha256": _sha256(DEFAULT_DIMENSION_REFERENCE),
        },
        "rows": rows,
        "total_all_four_collisions": sum(
            row["all_four_gates_accepted"] for row in rows
        ),
        "largest_passing_repeated_branch_family": largest_passing_branch_family,
        "first_combined_collision": first_collision,
        "status": "exact_twin_repair_broken_by_repeated_suborders",
        "claims_not_made": [
            "that every repeated branch order lacks a continuum embedding",
            "a general detector for repeated suborders",
            "sufficiency of any current gate combination",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(branch_adversary_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
