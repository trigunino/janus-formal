"""MF-KER-001: test whether weak relational axioms force two-order structure."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.program_m_dimension_two import polynomial_two_order_realizer
except ModuleNotFoundError:
    from program_m_dimension_two import polynomial_two_order_realizer


PROTOCOL = {
    "protocol_id": "MF-KER-001-v1",
    "base_seed": 2026071819,
    "rank": 16,
    "replicates": 256,
    "latent_dimensions": [2, 3],
}


def product_order(points: np.ndarray) -> np.ndarray:
    return np.all(points[:, None, :] <= points[None, :, :], axis=2)


def relabel(order: np.ndarray, permutation: np.ndarray) -> np.ndarray:
    return order[np.ix_(permutation, permutation)]


def is_partial_order(order: np.ndarray) -> bool:
    size = len(order)
    reflexive = np.all(np.diag(order))
    antisymmetric = not np.any((order & order.T) & ~np.eye(size, dtype=bool))
    transitive = np.all((order.astype(int) @ order.astype(int) == 0) | order)
    return bool(reflexive and antisymmetric and transitive)


def run_audit() -> dict[str, object]:
    rank = int(PROTOCOL["rank"])
    replicates = int(PROTOCOL["replicates"])
    rows = []
    for dimension in PROTOCOL["latent_dimensions"]:
        violations = order_failures = equivariance_failures = restriction_failures = 0
        for replicate in range(replicates):
            rng = np.random.default_rng(
                int(PROTOCOL["base_seed"]) + 100_000 * dimension + replicate
            )
            points = rng.random((rank, dimension))
            order = product_order(points)
            permutation = rng.permutation(rank)
            permuted_points = points[permutation]
            if not is_partial_order(order):
                order_failures += 1
            if not np.array_equal(product_order(permuted_points), relabel(order, permutation)):
                equivariance_failures += 1
            cutoff = rank // 2
            if not np.array_equal(product_order(points[:cutoff]), order[:cutoff, :cutoff]):
                restriction_failures += 1
            if polynomial_two_order_realizer(order) is None:
                violations += 1
        rows.append(
            {
                "latent_dimension": dimension,
                "replicates": replicates,
                "partial_order_failures": order_failures,
                "relabel_equivariance_failures": equivariance_failures,
                "projective_restriction_failures": restriction_failures,
                "dimension_two_violations": violations,
            }
        )
    by_dimension = {row["latent_dimension"]: row for row in rows}
    weak_axioms_hold = all(
        row[key] == 0
        for row in rows
        for key in (
            "partial_order_failures",
            "relabel_equivariance_failures",
            "projective_restriction_failures",
        )
    )
    return {
        "program": "MF-KER-001",
        "protocol": PROTOCOL,
        "weak_base": ["partial_order", "exchangeable_relabelling", "projective_restriction"],
        "rows": rows,
        "gates": {
            "weak_axioms_hold_for_both_models": weak_axioms_hold,
            "two_coordinate_model_is_dimension_two":
                by_dimension[2]["dimension_two_violations"] == 0,
            "three_coordinate_countermodel_breaks_dimension_two":
                by_dimension[3]["dimension_two_violations"] > 0,
        },
        "conclusion": (
            "partial order, exchangeability and projectivity do not force a "
            "two-order representation"
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
