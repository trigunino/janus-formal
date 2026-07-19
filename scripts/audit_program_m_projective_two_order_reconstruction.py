"""MF-REP-003: coherent restriction of an intrinsic two-order realizer."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_decorated_layer_adversary import decorated_layer_order
    from scripts.audit_program_m_ensemble_separation import minkowski_order
    from scripts.audit_program_m_six_point_dimension_obstruction import (
        is_standard_s3,
        product_order_3d,
    )
    from scripts.audit_program_m_three_symmetric_permuton import three_symmetric_permuton_order
    from scripts.audit_program_m_two_order_representation import (
        linear_order_matrix,
        two_order_realizer_fast,
    )
except ModuleNotFoundError:
    from audit_program_m_decorated_layer_adversary import decorated_layer_order
    from audit_program_m_ensemble_separation import minkowski_order
    from audit_program_m_six_point_dimension_obstruction import is_standard_s3, product_order_3d
    from audit_program_m_three_symmetric_permuton import three_symmetric_permuton_order
    from audit_program_m_two_order_representation import linear_order_matrix, two_order_realizer_fast


PROTOCOL = {
    "protocol_id": "MF-REP-003-v1",
    "base_seed": 2026071813,
    "nested_sizes": [6, 8, 10],
    "replicates": 32,
}


def restrict_permutation(permutation: tuple[int, ...], size: int) -> tuple[int, ...]:
    return tuple(point for point in permutation if point < size)


def realizes(order: np.ndarray, realizer: tuple[tuple[int, ...], tuple[int, ...]]) -> bool:
    return bool(
        np.array_equal(
            linear_order_matrix(realizer[0]) & linear_order_matrix(realizer[1]), order
        )
    )


def contains_s3(order: np.ndarray) -> bool:
    return any(
        is_standard_s3(order[np.ix_(subset, subset)])
        for subset in itertools.combinations(range(len(order)), 6)
    )


def run_audit() -> dict[str, object]:
    models = (
        ("minkowski_1p1", minkowski_order),
        ("three_symmetric_permuton", three_symmetric_permuton_order),
        ("decorated_layer", decorated_layer_order),
        ("product_order_3d", product_order_3d),
    )
    largest = max(PROTOCOL["nested_sizes"])
    rows = []
    for model_index, (name, generator) in enumerate(models):
        realized = coherent = s3_obstructed = 0
        for replicate in range(int(PROTOCOL["replicates"])):
            rng = np.random.default_rng(
                int(PROTOCOL["base_seed"]) + 1_000_000 * model_index + replicate
            )
            order = generator(largest, rng)
            if contains_s3(order):
                s3_obstructed += 1
                continue
            realizer = two_order_realizer_fast(order)
            if realizer is None:
                continue
            realized += 1
            if all(
                realizes(
                    order[:size, :size],
                    (restrict_permutation(realizer[0], size), restrict_permutation(realizer[1], size)),
                )
                for size in PROTOCOL["nested_sizes"]
            ):
                coherent += 1
        rows.append(
            {
                "model": name,
                "replicates": int(PROTOCOL["replicates"]),
                "largest_sample_two_order_realizable": realized,
                "coherent_on_all_nested_sizes": coherent,
                "rejected_by_explicit_s3": s3_obstructed,
            }
        )
    by_model = {row["model"]: row for row in rows}
    return {
        "program": "MF-REP-003",
        "protocol": PROTOCOL,
        "rows": rows,
        "gates": {
            "minkowski_all_coherent": by_model["minkowski_1p1"]["coherent_on_all_nested_sizes"]
                == int(PROTOCOL["replicates"]),
            "nonuniform_two_order_adversary_all_coherent":
                by_model["three_symmetric_permuton"]["coherent_on_all_nested_sizes"]
                == int(PROTOCOL["replicates"]),
            "restriction_never_breaks_a_found_realizer": all(
                row["coherent_on_all_nested_sizes"]
                == row["largest_sample_two_order_realizable"] for row in rows
            ),
        },
        "scope": (
            "finite nested reconstruction; compactness gives a global dimension-two "
            "representation only if every finite induced subposet is realizable"
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
