"""MF-DIM-001B: simultaneous sequential dimension audit at ranks 6--8."""

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
    from scripts.audit_program_m_two_order_representation import two_order_realizer_fast
except ModuleNotFoundError:
    from audit_program_m_decorated_layer_adversary import decorated_layer_order
    from audit_program_m_ensemble_separation import minkowski_order
    from audit_program_m_sequential_evidence import clopper_pearson_interval
    from audit_program_m_six_point_dimension_obstruction import product_order_3d
    from audit_program_m_three_symmetric_permuton import three_symmetric_permuton_order
    from audit_program_m_two_order_representation import two_order_realizer_fast


PROTOCOL = {
    "protocol_id": "MF-DIM-001B-v1",
    "base_seed": 2026071816,
    "ranks": [6, 7, 8],
    "checkpoints": [256, 1024, 4096],
    "models": [
        "minkowski_1p1", "three_symmetric_permuton", "decorated_layer", "product_order_3d"
    ],
    "family_alpha": 0.05,
    "alpha_spending": "alpha_(model,rank,s) = 0.05 / (4*3*s*(s+1))",
}


def allocated_alpha(stage: int) -> float:
    return float(PROTOCOL["family_alpha"]) / (
        len(PROTOCOL["models"]) * len(PROTOCOL["ranks"]) * stage * (stage + 1)
    )


def run_audit() -> dict[str, object]:
    models = (
        ("minkowski_1p1", minkowski_order),
        ("three_symmetric_permuton", three_symmetric_permuton_order),
        ("decorated_layer", decorated_layer_order),
        ("product_order_3d", product_order_3d),
    )
    rows = []
    for model_index, (name, generator) in enumerate(models):
        rank_rows = []
        for rank in PROTOCOL["ranks"]:
            rng = np.random.default_rng(
                int(PROTOCOL["base_seed"]) + 1_000_000 * model_index + 10_000 * rank
            )
            violations = 0
            previous = 0
            stages = []
            for stage, checkpoint in enumerate(PROTOCOL["checkpoints"], start=1):
                for _ in range(checkpoint - previous):
                    order = generator(rank, rng)
                    violations += int(two_order_realizer_fast(order) is None)
                alpha = allocated_alpha(stage)
                interval = clopper_pearson_interval(violations, checkpoint, alpha)
                stages.append(
                    {
                        "checkpoint": checkpoint,
                        "violations": violations,
                        "frequency": violations / checkpoint,
                        "probability_interval": list(interval),
                        "allocated_alpha": alpha,
                    }
                )
                previous = checkpoint
            rank_rows.append({"rank": rank, "stages": stages})
        rows.append({"model": name, "ranks": rank_rows})

    final = {
        row["model"]: {rank_row["rank"]: rank_row["stages"][-1] for rank_row in row["ranks"]}
        for row in rows
    }
    return {
        "program": "MF-DIM-001B",
        "protocol": PROTOCOL,
        "rows": rows,
        "gates": {
            "minkowski_no_observed_violation_at_any_rank": all(
                final["minkowski_1p1"][rank]["violations"] == 0 for rank in PROTOCOL["ranks"]
            ),
            "minkowski_all_upper_bounds_below_0p003": all(
                final["minkowski_1p1"][rank]["probability_interval"][1] < 0.003
                for rank in PROTOCOL["ranks"]
            ),
            "known_two_order_adversary_no_violation": all(
                final["three_symmetric_permuton"][rank]["violations"] == 0
                for rank in PROTOCOL["ranks"]
            ),
            "three_dimensional_lower_bound_positive_at_rank_7":
                final["product_order_3d"][7]["probability_interval"][0] > 0,
            "three_dimensional_lower_bound_positive_at_rank_8":
                final["product_order_3d"][8]["probability_interval"][0] > 0,
        },
        "scope": (
            "simultaneous over all models, ranks and checkpoints; ranks above eight "
            "remain untested, so the universal dimension-two premise is not proved"
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
