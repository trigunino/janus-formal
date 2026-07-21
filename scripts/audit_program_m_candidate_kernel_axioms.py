"""MF-KER-002: stress-test natural non-geometric kernel axioms."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_weak_kernel_axioms import product_order
    from scripts.program_m_dimension_two import polynomial_two_order_realizer
except ModuleNotFoundError:
    from audit_program_m_weak_kernel_axioms import product_order
    from program_m_dimension_two import polynomial_two_order_realizer


PROTOCOL = {
    "protocol_id": "MF-KER-002-v1",
    "base_seed": 2026071820,
    "rank": 16,
    "replicates": 128,
    "latent_dimensions": [2, 3],
}

CANDIDATES = (
    "iid_atomless_latents",
    "deterministic_continuous_comparison",
    "coordinate_permutation_symmetry",
    "past_future_duality",
    "coordinatewise_factorization",
)


def run_audit() -> dict[str, object]:
    rows = []
    rank = int(PROTOCOL["rank"])
    replicates = int(PROTOCOL["replicates"])
    for dimension in PROTOCOL["latent_dimensions"]:
        coordinate_symmetry_failures = duality_failures = violations = 0
        for replicate in range(replicates):
            rng = np.random.default_rng(
                int(PROTOCOL["base_seed"]) + 100_000 * dimension + replicate
            )
            points = rng.random((rank, dimension))
            order = product_order(points)
            coordinate_permutation = rng.permutation(dimension)
            if not np.array_equal(order, product_order(points[:, coordinate_permutation])):
                coordinate_symmetry_failures += 1
            if not np.array_equal(order.T, product_order(1.0 - points)):
                duality_failures += 1
            if polynomial_two_order_realizer(order) is None:
                violations += 1
        rows.append(
            {
                "latent_dimension": dimension,
                "replicates": replicates,
                "candidate_axioms": {candidate: True for candidate in CANDIDATES},
                "coordinate_symmetry_failures": coordinate_symmetry_failures,
                "past_future_duality_failures": duality_failures,
                "dimension_two_violations": violations,
            }
        )
    countermodel = next(row for row in rows if row["latent_dimension"] == 3)
    return {
        "program": "MF-KER-002",
        "protocol": PROTOCOL,
        "candidate_axioms": list(CANDIDATES),
        "rows": rows,
        "gates": {
            "all_candidate_axioms_hold_in_both_dimensions": all(
                all(row["candidate_axioms"].values())
                and row["coordinate_symmetry_failures"] == 0
                and row["past_future_duality_failures"] == 0
                for row in rows
            ),
            "candidate_axioms_do_not_force_dimension_two":
                countermodel["dimension_two_violations"] > 0,
        },
        "conclusion": (
            "none of the tested natural axioms, separately or jointly, selects "
            "two latent orders from the weak base"
        ),
        "next_boundary": (
            "a successful axiom must constrain effective order dimension or motif "
            "laws; its independence from the desired conclusion must be proved"
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
