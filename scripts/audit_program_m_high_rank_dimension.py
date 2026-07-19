"""MF-DIM-002: polynomial two-order recognition through rank 64."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_decorated_layer_adversary import decorated_layer_order
    from scripts.audit_program_m_ensemble_separation import minkowski_order
    from scripts.audit_program_m_sequential_evidence import clopper_pearson_interval
    from scripts.audit_program_m_six_point_dimension_obstruction import product_order_3d
    from scripts.audit_program_m_three_symmetric_permuton import three_symmetric_permuton_order
    from scripts.program_m_dimension_two import polynomial_two_order_realizer
except ModuleNotFoundError:
    from audit_program_m_decorated_layer_adversary import decorated_layer_order
    from audit_program_m_ensemble_separation import minkowski_order
    from audit_program_m_sequential_evidence import clopper_pearson_interval
    from audit_program_m_six_point_dimension_obstruction import product_order_3d
    from audit_program_m_three_symmetric_permuton import three_symmetric_permuton_order
    from program_m_dimension_two import polynomial_two_order_realizer


PROTOCOL = {
    "protocol_id": "MF-DIM-002-v1",
    "base_seed": 2026071817,
    "ranks": [8, 12, 16, 24, 32, 48, 64],
    "samples_per_model_rank": 512,
    "models": [
        "minkowski_1p1", "three_symmetric_permuton", "decorated_layer", "product_order_3d"
    ],
    "family_alpha": 0.05,
    "cell_alpha": 0.05 / 28,
}


def run_audit() -> dict[str, object]:
    models = (
        ("minkowski_1p1", minkowski_order),
        ("three_symmetric_permuton", three_symmetric_permuton_order),
        ("decorated_layer", decorated_layer_order),
        ("product_order_3d", product_order_3d),
    )
    rows = []
    samples = int(PROTOCOL["samples_per_model_rank"])
    for model_index, (name, generator) in enumerate(models):
        rank_rows = []
        for rank in PROTOCOL["ranks"]:
            rng = np.random.default_rng(
                int(PROTOCOL["base_seed"]) + 1_000_000 * model_index + 10_000 * rank
            )
            violations = sum(
                polynomial_two_order_realizer(generator(rank, rng)) is None
                for _ in range(samples)
            )
            interval = clopper_pearson_interval(
                violations, samples, float(PROTOCOL["cell_alpha"])
            )
            rank_rows.append(
                {
                    "rank": rank,
                    "samples": samples,
                    "violations": violations,
                    "frequency": violations / samples,
                    "probability_interval": list(interval),
                }
            )
        rows.append({"model": name, "ranks": rank_rows})
    by_model = {row["model"]: row["ranks"] for row in rows}
    return {
        "program": "MF-DIM-002",
        "protocol": PROTOCOL,
        "validation": {
            "polynomial_vs_exhaustive": "exact agreement on 4824 naturally labelled rank-6 posets",
            "positive_certificate": "returned linear orders are re-intersected with the input poset",
        },
        "rows": rows,
        "gates": {
            "minkowski_no_violation_through_rank_64": all(
                row["violations"] == 0 for row in by_model["minkowski_1p1"]
            ),
            "known_two_order_adversary_no_violation_through_rank_64": all(
                row["violations"] == 0 for row in by_model["three_symmetric_permuton"]
            ),
            "decorated_adversary_rejected_by_rank_12":
                next(row for row in by_model["decorated_layer"] if row["rank"] == 12)["violations"] > 0,
            "three_dimensional_control_rejected_by_rank_12":
                next(row for row in by_model["product_order_3d"] if row["rank"] == 12)["violations"] > 0,
        },
        "scope": (
            "finite ranks through 64 with simultaneous fixed-cell intervals; no "
            "finite maximum rank proves the universal dimension-two premise"
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
