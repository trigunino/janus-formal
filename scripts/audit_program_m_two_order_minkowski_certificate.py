"""MF-CERT-001: combine intrinsic two-order reconstruction and rank-four law."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_decorated_layer_adversary import decorated_layer_order
    from scripts.audit_program_m_ensemble_separation import minkowski_order
    from scripts.audit_program_m_pattern_ladder import (
        exact_minkowski_distribution,
        sampled_distribution,
        total_variation,
    )
    from scripts.audit_program_m_six_point_dimension_obstruction import product_order_3d
    from scripts.audit_program_m_three_symmetric_permuton import three_symmetric_permuton_order
    from scripts.audit_program_m_two_order_representation import two_order_realizer_fast
except ModuleNotFoundError:
    from audit_program_m_decorated_layer_adversary import decorated_layer_order
    from audit_program_m_ensemble_separation import minkowski_order
    from audit_program_m_pattern_ladder import exact_minkowski_distribution, sampled_distribution, total_variation
    from audit_program_m_six_point_dimension_obstruction import product_order_3d
    from audit_program_m_three_symmetric_permuton import three_symmetric_permuton_order
    from audit_program_m_two_order_representation import two_order_realizer_fast


PROTOCOL = {
    "protocol_id": "MF-CERT-001-v1",
    "base_seed": 2026071814,
    "replicates": 32,
    "reconstruction_size": 10,
    "pattern_rank": 4,
    "patterns_per_replicate": 8192,
    "frozen_rank_four_tv_threshold": 0.024495442708333332,
    "threshold_source": "MF-ADV-009 independent Minkowski calibration",
}


def run_audit() -> dict[str, object]:
    models = (
        ("minkowski_1p1", minkowski_order),
        ("three_symmetric_permuton", three_symmetric_permuton_order),
        ("decorated_layer", decorated_layer_order),
        ("product_order_3d", product_order_3d),
    )
    reference = exact_minkowski_distribution(int(PROTOCOL["pattern_rank"]))
    rows = []
    for model_index, (name, generator) in enumerate(models):
        reconstruction_passes = pattern_passes = combined_passes = 0
        distances = []
        for replicate in range(int(PROTOCOL["replicates"])):
            seed = int(PROTOCOL["base_seed"]) + 1_000_000 * model_index + replicate
            order = generator(
                int(PROTOCOL["reconstruction_size"]), np.random.default_rng(seed)
            )
            reconstruction_ok = two_order_realizer_fast(order) is not None
            distance = total_variation(
                sampled_distribution(
                    generator,
                    int(PROTOCOL["pattern_rank"]),
                    int(PROTOCOL["patterns_per_replicate"]),
                    seed + 100_000_000,
                ),
                reference,
            )
            pattern_ok = distance <= float(PROTOCOL["frozen_rank_four_tv_threshold"])
            distances.append(distance)
            reconstruction_passes += int(reconstruction_ok)
            pattern_passes += int(pattern_ok)
            combined_passes += int(reconstruction_ok and pattern_ok)
        rows.append(
            {
                "model": name,
                "replicates": int(PROTOCOL["replicates"]),
                "two_order_reconstruction_passes": reconstruction_passes,
                "rank_four_pattern_passes": pattern_passes,
                "combined_passes": combined_passes,
                "mean_rank_four_total_variation": float(np.mean(distances)),
            }
        )
    by_model = {row["model"]: row for row in rows}
    return {
        "program": "MF-CERT-001",
        "protocol": PROTOCOL,
        "rows": rows,
        "gates": {
            "target_combined_acceptance_at_least_0p90":
                by_model["minkowski_1p1"]["combined_passes"] >= 29,
            "three_symmetric_adversary_combined_acceptance_zero":
                by_model["three_symmetric_permuton"]["combined_passes"] == 0,
            "decorated_adversary_combined_acceptance_zero":
                by_model["decorated_layer"]["combined_passes"] == 0,
            "three_coordinate_control_combined_acceptance_zero":
                by_model["product_order_3d"]["combined_passes"] == 0,
        },
        "logical_scope": (
            "finite statistical certificate only; exact global identification additionally "
            "requires every finite subposet to have dimension at most two, compactness, "
            "exchangeability, continuity, and the published rank-four forcing theorem"
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
