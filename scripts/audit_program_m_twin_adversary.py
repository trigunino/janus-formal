"""MF-ADV-002: engineered twin-class attack on all order-only gates."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_adversarial_orders import DEFAULT_LINK_REFERENCE
    from scripts.audit_program_m_blind_dimension import order_matrix_from_null_points
    from scripts.audit_program_m_intrinsic_link_fluctuations import (
        intrinsic_link_fluctuation,
    )
    from scripts.evaluate_program_m_order_candidate import (
        DEFAULT_DIMENSION_REFERENCE,
        DEFAULT_LOCALITY_REFERENCE,
        evaluate_order,
    )
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_adversarial_orders import DEFAULT_LINK_REFERENCE
    from audit_program_m_blind_dimension import order_matrix_from_null_points
    from audit_program_m_intrinsic_link_fluctuations import intrinsic_link_fluctuation
    from evaluate_program_m_order_candidate import (
        DEFAULT_DIMENSION_REFERENCE,
        DEFAULT_LOCALITY_REFERENCE,
        evaluate_order,
    )


PROTOCOL = {
    "protocol_id": "MF-ADV-002-v1",
    "cardinality": 256,
    "base_seed": 2026102400,
    "clone_multiplicities": [2, 4, 6, 8, 10, 12],
    "fresh_validation_replicates": 40,
    "cloned_base_vertex": 0,
    "pilot_seeds_excluded": True,
}


def clone_vertex_order(clone_multiplicity: int, seed: int) -> np.ndarray:
    final_size = int(PROTOCOL["cardinality"])
    base_size = final_size - clone_multiplicity + 1
    points = np.random.default_rng(seed).random((base_size, 2))
    base = order_matrix_from_null_points(points)
    del points
    result = np.zeros((final_size, final_size), dtype=bool)
    result[:clone_multiplicity, :clone_multiplicity] = np.eye(
        clone_multiplicity, dtype=bool
    )
    result[clone_multiplicity:, clone_multiplicity:] = base[1:, 1:]
    for base_vertex in range(1, base_size):
        output_vertex = clone_multiplicity + base_vertex - 1
        for clone in range(clone_multiplicity):
            result[clone, output_vertex] = base[0, base_vertex]
            result[output_vertex, clone] = base[base_vertex, 0]
    return result


def twin_classes(order: np.ndarray) -> list[list[int]]:
    matrix = np.asarray(order, dtype=bool)
    signatures: dict[tuple[bytes, bytes], list[int]] = {}
    for vertex in range(len(matrix)):
        future = matrix[vertex].copy()
        past = matrix[:, vertex].copy()
        future[vertex] = False
        past[vertex] = False
        signatures.setdefault((future.tobytes(), past.tobytes()), []).append(vertex)
    return sorted(
        (vertices for vertices in signatures.values() if len(vertices) > 1),
        key=lambda vertices: (-len(vertices), vertices),
    )


def _load(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def twin_adversary_audit(
    *,
    link_reference_path: Path = DEFAULT_LINK_REFERENCE,
    locality_reference_path: Path = DEFAULT_LOCALITY_REFERENCE,
    dimension_reference_path: Path = DEFAULT_DIMENSION_REFERENCE,
) -> dict[str, object]:
    link_reference = _load(link_reference_path)
    locality_reference = _load(locality_reference_path)
    dimension_reference = _load(dimension_reference_path)
    size = int(PROTOCOL["cardinality"])
    link_row = next(row for row in link_reference["rows"] if row["cardinality"] == size)
    link_lower, link_upper = link_row["acceptance_interval"]
    rows = []
    first_collision = None
    largest_passing_twin_class = 0
    for multiplicity in PROTOCOL["clone_multiplicities"]:
        counts = {
            "generated": 0,
            "link_accepted": 0,
            "dimension_accepted": 0,
            "locality_accepted": 0,
            "all_three_accepted": 0,
        }
        for replicate in range(int(PROTOCOL["fresh_validation_replicates"])):
            seed = int(PROTOCOL["base_seed"]) + 1_000 * multiplicity + replicate
            order = clone_vertex_order(multiplicity, seed)
            classes = twin_classes(order)
            observed_multiplicity = len(classes[0]) if classes else 1
            link_score = intrinsic_link_fluctuation(order)
            link_accepted = link_lower <= link_score <= link_upper
            report = evaluate_order(
                order,
                locality_reference=locality_reference,
                dimension_reference=dimension_reference,
                source_name=f"twin_class:{multiplicity}:seed={seed}",
            )
            dimension_accepted = bool(
                report["diagnostics"]["myrheim_meyer_dimension"]["accepted"]
            )
            locality_accepted = bool(
                report["diagnostics"]["interval_abundance"]["accepted"]
            )
            all_three = link_accepted and dimension_accepted and locality_accepted
            counts["generated"] += 1
            counts["link_accepted"] += int(link_accepted)
            counts["dimension_accepted"] += int(dimension_accepted)
            counts["locality_accepted"] += int(locality_accepted)
            counts["all_three_accepted"] += int(all_three)
            if all_three:
                largest_passing_twin_class = max(
                    largest_passing_twin_class, observed_multiplicity
                )
                if first_collision is None:
                    first_collision = {
                        "requested_clone_multiplicity": multiplicity,
                        "observed_largest_twin_class": observed_multiplicity,
                        "seed": seed,
                        "order_sha256": report["order_sha256"],
                        "link_score": link_score,
                        "dimension": report["diagnostics"]["myrheim_meyer_dimension"],
                        "locality": report["diagnostics"]["interval_abundance"],
                    }
        rows.append({"clone_multiplicity": multiplicity, **counts})
    totals = {
        key: sum(row[key] for row in rows)
        for key in (
            "generated",
            "link_accepted",
            "dimension_accepted",
            "locality_accepted",
            "all_three_accepted",
        )
    }
    return {
        "program": "MF-ADV-002",
        "protocol": PROTOCOL,
        "construction": (
            "replace one element of a fresh conditioned-Poisson order by a named "
            "antichain of exact past/future twins"
        ),
        "references": {
            "link_sha256": _sha256(link_reference_path),
            "locality_sha256": _sha256(locality_reference_path),
            "dimension_sha256": _sha256(dimension_reference_path),
        },
        "rows": rows,
        "totals": totals,
        "largest_twin_class_in_a_three_gate_collision": largest_passing_twin_class,
        "first_combined_collision": first_collision,
        "status": "combined_order_only_gate_broken",
        "conclusion": (
            "engineered exact twins survive all three frozen order-only diagnostics; "
            "their low-order summaries do not certify generic Poisson structure"
        ),
        "claims_not_made": [
            "that twin classes are impossible in every continuum sprinkling order",
            "that every passing clone order lacks every geometric embedding",
            "a calibrated twin-class rejection threshold",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(twin_adversary_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
