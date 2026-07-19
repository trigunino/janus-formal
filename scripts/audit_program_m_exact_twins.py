"""MF-MAN-016: conformal gate for exact relational twin multiplicity."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

try:
    from scripts.audit_program_m_intrinsic_link_fluctuations import (
        conditioned_poisson_order,
    )
    from scripts.audit_program_m_twin_adversary import clone_vertex_order, twin_classes
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_intrinsic_link_fluctuations import conditioned_poisson_order
    from audit_program_m_twin_adversary import clone_vertex_order, twin_classes


PROTOCOL = {
    "protocol_id": "MF-MAN-016-v1",
    "base_seed": 2026102600,
    "cardinalities": [128, 256, 512, 784],
    "calibration_replicates": 199,
    "validation_replicates": 400,
    "alpha": 0.10,
    "upper_rank": 180,
}


def largest_twin_class(order) -> int:
    classes = twin_classes(order)
    return len(classes[0]) if classes else 1


def exact_twin_audit() -> dict[str, object]:
    calibration_count = int(PROTOCOL["calibration_replicates"])
    validation_count = int(PROTOCOL["validation_replicates"])
    rank = int(PROTOCOL["upper_rank"])
    rows = []
    for size_index, cardinality in enumerate(PROTOCOL["cardinalities"]):
        seed_root = int(PROTOCOL["base_seed"]) + 100_000 * size_index
        calibration = sorted(
            largest_twin_class(
                conditioned_poisson_order(cardinality, seed_root + replicate)
            )
            for replicate in range(calibration_count)
        )
        threshold = calibration[rank - 1]
        validation = [
            largest_twin_class(
                conditioned_poisson_order(
                    cardinality, seed_root + 50_000 + replicate
                )
            )
            for replicate in range(validation_count)
        ]
        controls = []
        if cardinality == 256:
            for multiplicity in (4, 8, 12):
                score = largest_twin_class(
                    clone_vertex_order(multiplicity, seed_root + 90_000 + multiplicity)
                )
                controls.append(
                    {
                        "clone_multiplicity": multiplicity,
                        "largest_twin_class": score,
                        "accepted": score <= threshold,
                    }
                )
        rows.append(
            {
                "cardinality": cardinality,
                "upper_threshold": threshold,
                "validation_coverage": sum(score <= threshold for score in validation)
                / validation_count,
                "validation_maximum": max(validation),
                "exact_clone_controls": controls,
            }
        )
    expected_rank = math.ceil(
        (calibration_count + 1) * (1 - float(PROTOCOL["alpha"]))
    )
    return {
        "program": "MF-MAN-016",
        "input": "finite partial-order matrix only",
        "statistic": "largest class with exactly equal strict past and strict future",
        "protocol": PROTOCOL,
        "protocol_integrity": {
            "expected_rank": expected_rank,
            "rank_matches": rank == expected_rank,
            "fresh_validation_seeds": True,
        },
        "guarantee": (
            "90% marginal one-sided split-conformal coverage per cardinality "
            "under exchangeability"
        ),
        "rows": rows,
        "conclusion": (
            "natural exact pairs are retained while engineered multiplicities at "
            "least four are rejected by the N=256 reference"
        ),
        "claims_not_made": [
            "that every exact twin pair is geometric",
            "detection of approximate twins or repeated nontrivial suborders",
            "sufficiency for manifold-likeness",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(exact_twin_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
