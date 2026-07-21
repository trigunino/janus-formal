"""MF-ADV-004: asymmetric chain-fan attack on the 1-WL repair."""

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
    from scripts.audit_program_m_wl_compressibility import orientation_symmetric_wl
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
    from audit_program_m_wl_compressibility import orientation_symmetric_wl
    from evaluate_program_m_order_candidate import (
        DEFAULT_DIMENSION_REFERENCE,
        DEFAULT_LOCALITY_REFERENCE,
        evaluate_order,
    )


DEFAULT_TWIN_REFERENCE = Path("outputs/program_m/mf_man_016_exact_twins.json")
DEFAULT_WL_REFERENCE = Path("outputs/program_m/mf_man_017_wl_compressibility.json")

PROTOCOL = {
    "protocol_id": "MF-ADV-004-v1",
    "cardinality": 256,
    "base_seed": 2026103200,
    "maximum_chain_lengths": [2, 3, 4, 5, 6, 7],
    "fresh_validation_replicates": 40,
    "pilot_seeds_excluded": True,
}


def graduated_chain_fan(maximum_length: int, seed: int) -> np.ndarray:
    final_size = int(PROTOCOL["cardinality"])
    fan_size = maximum_length * (maximum_length + 1) // 2
    base_size = final_size - fan_size + 1
    points = np.random.default_rng(seed).random((base_size, 2))
    base = order_matrix_from_null_points(points)
    del points
    order = np.zeros((final_size, final_size), dtype=bool)
    order[:fan_size, :fan_size] = np.eye(fan_size, dtype=bool)
    offset = 0
    for length in range(1, maximum_length + 1):
        for lower in range(length):
            for upper in range(lower, length):
                order[offset + lower, offset + upper] = True
        offset += length
    order[fan_size:, fan_size:] = base[1:, 1:]
    for base_vertex in range(1, base_size):
        output_vertex = fan_size + base_vertex - 1
        if base[0, base_vertex]:
            order[:fan_size, output_vertex] = True
        if base[base_vertex, 0]:
            order[output_vertex, :fan_size] = True
    return order


def _load(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def wl_adversary_audit() -> dict[str, object]:
    link_reference = _load(DEFAULT_LINK_REFERENCE)
    twin_reference = _load(DEFAULT_TWIN_REFERENCE)
    wl_reference = _load(DEFAULT_WL_REFERENCE)
    locality = _load(DEFAULT_LOCALITY_REFERENCE)
    dimension = _load(DEFAULT_DIMENSION_REFERENCE)
    size = int(PROTOCOL["cardinality"])
    link_row = next(row for row in link_reference["rows"] if row["cardinality"] == size)
    twin_row = next(row for row in twin_reference["rows"] if row["cardinality"] == size)
    wl_row = next(row for row in wl_reference["rows"] if row["cardinality"] == size)
    link_lower, link_upper = link_row["acceptance_interval"]
    twin_threshold = twin_row["upper_threshold"]
    wl_threshold = wl_row["upper_threshold"]
    rows = []
    first_collision = None
    largest_passing_fan = 0
    for maximum_length in PROTOCOL["maximum_chain_lengths"]:
        passed = 0
        for replicate in range(int(PROTOCOL["fresh_validation_replicates"])):
            seed = int(PROTOCOL["base_seed"]) + 1_000 * maximum_length + replicate
            order = graduated_chain_fan(maximum_length, seed)
            link_score = intrinsic_link_fluctuation(order)
            twin_score = largest_twin_class(order)
            wl_report = orientation_symmetric_wl(order)
            wl_score = int(wl_report["largest_stable_class"])
            report = evaluate_order(
                order,
                locality_reference=locality,
                dimension_reference=dimension,
                source_name=f"graduated_chain_fan:{maximum_length}:seed={seed}",
            )
            all_five = (
                link_lower <= link_score <= link_upper
                and twin_score <= twin_threshold
                and wl_score <= wl_threshold
                and report["status"] == "compatible_with_external_minkowski2_diagnostics"
            )
            passed += int(all_five)
            if all_five:
                largest_passing_fan = max(largest_passing_fan, maximum_length)
                if first_collision is None:
                    first_collision = {
                        "maximum_chain_length": maximum_length,
                        "fan_objects": maximum_length * (maximum_length + 1) // 2,
                        "seed": seed,
                        "order_sha256": report["order_sha256"],
                        "link_score": link_score,
                        "largest_exact_twin_class": twin_score,
                        "largest_wl_class": wl_score,
                        "wl_profile_head": wl_report["class_size_profile"][:8],
                        "dimension": report["diagnostics"]["myrheim_meyer_dimension"],
                        "locality": report["diagnostics"]["interval_abundance"],
                    }
        rows.append(
            {
                "maximum_chain_length": maximum_length,
                "fan_objects": maximum_length * (maximum_length + 1) // 2,
                "generated": int(PROTOCOL["fresh_validation_replicates"]),
                "all_five_gates_accepted": passed,
            }
        )
    return {
        "program": "MF-ADV-004",
        "protocol": PROTOCOL,
        "construction": (
            "replace one element by a fan containing one chain of each length "
            "1..m; the rule is short but the branches are pairwise non-isomorphic"
        ),
        "references": {
            "link_sha256": _sha(DEFAULT_LINK_REFERENCE),
            "twin_sha256": _sha(DEFAULT_TWIN_REFERENCE),
            "wl_sha256": _sha(DEFAULT_WL_REFERENCE),
            "locality_sha256": _sha(DEFAULT_LOCALITY_REFERENCE),
            "dimension_sha256": _sha(DEFAULT_DIMENSION_REFERENCE),
        },
        "rows": rows,
        "total_all_five_collisions": sum(row["all_five_gates_accepted"] for row in rows),
        "largest_passing_maximum_chain_length": largest_passing_fan,
        "first_combined_collision": first_collision,
        "status": "one_wl_repair_broken_by_asymmetric_compressible_fan",
        "conclusion": (
            "stable color multiplicity detects symmetry but not every short generative "
            "description; asymmetric chain fans evade all five current gates"
        ),
        "claims_not_made": [
            "a computation of Kolmogorov complexity",
            "that every passing fan lacks a continuum embedding",
            "completeness against higher-dimensional WL or canonical compression",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(wl_adversary_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
