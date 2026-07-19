"""MF-STAT-001: preregistered sequential bounds for two exact premises."""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from pathlib import Path

import numpy as np
from scipy.stats import beta

try:
    from scripts.audit_program_m_decorated_layer_adversary import decorated_layer_order
    from scripts.audit_program_m_ensemble_separation import minkowski_order
    from scripts.audit_program_m_pattern_ladder import (
        canonical_mask,
        exact_minkowski_distribution,
        relation_mask,
        total_variation,
    )
    from scripts.audit_program_m_six_point_dimension_obstruction import product_order_3d
    from scripts.audit_program_m_three_symmetric_permuton import three_symmetric_permuton_order
    from scripts.audit_program_m_two_order_representation import two_order_realizer_fast
except ModuleNotFoundError:
    from audit_program_m_decorated_layer_adversary import decorated_layer_order
    from audit_program_m_ensemble_separation import minkowski_order
    from audit_program_m_pattern_ladder import canonical_mask, exact_minkowski_distribution, relation_mask, total_variation
    from audit_program_m_six_point_dimension_obstruction import product_order_3d
    from audit_program_m_three_symmetric_permuton import three_symmetric_permuton_order
    from audit_program_m_two_order_representation import two_order_realizer_fast


PROTOCOL = {
    "protocol_id": "MF-STAT-001-v1",
    "base_seed": 2026071815,
    "checkpoints": [256, 1024, 4096, 16384],
    "dimension_rank": 6,
    "pattern_rank": 4,
    "family_alpha": 0.05,
    "dimension_alpha": 0.025,
    "pattern_alpha": 0.025,
    "alpha_spending": "alpha_(model,s) = family_component / (4 s(s+1))",
}


def stage_alpha(component_alpha: float, stage: int) -> float:
    return component_alpha / (stage * (stage + 1))


def clopper_pearson_interval(successes: int, trials: int, alpha: float) -> tuple[float, float]:
    tail = alpha / 2
    lower = 0.0 if successes == 0 else float(beta.ppf(tail, successes, trials - successes + 1))
    upper = 1.0 if successes == trials else float(beta.ppf(1 - tail, successes + 1, trials - successes))
    return lower, upper


def weissman_tv_radius(pattern_count: int, samples: int, alpha: float) -> float:
    # P(||p_hat-p||_1 >= eps) <= (2^K-2) exp(-N eps^2/2).
    return math.sqrt((math.log(2**pattern_count - 2) + math.log(1 / alpha)) / (2 * samples))


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
        dimension_rng = np.random.default_rng(int(PROTOCOL["base_seed"]) + 1_000_000 * model_index)
        pattern_rng = np.random.default_rng(int(PROTOCOL["base_seed"]) + 1_000_000 * model_index + 500_000)
        violations = 0
        pattern_counts: Counter[int] = Counter()
        previous = 0
        stages = []
        for stage, checkpoint in enumerate(PROTOCOL["checkpoints"], start=1):
            for _ in range(checkpoint - previous):
                dimension_order = generator(int(PROTOCOL["dimension_rank"]), dimension_rng)
                violations += int(two_order_realizer_fast(dimension_order) is None)
                pattern_order = generator(int(PROTOCOL["pattern_rank"]), pattern_rng)
                pattern_counts[
                    canonical_mask(
                        int(PROTOCOL["pattern_rank"]), relation_mask(pattern_order)
                    )
                ] += 1
            dimension_alpha = stage_alpha(float(PROTOCOL["dimension_alpha"]), stage) / len(models)
            pattern_alpha = stage_alpha(float(PROTOCOL["pattern_alpha"]), stage) / len(models)
            violation_interval = clopper_pearson_interval(violations, checkpoint, dimension_alpha)
            empirical = {key: count / checkpoint for key, count in pattern_counts.items()}
            observed_tv = total_variation(empirical, reference)
            radius = weissman_tv_radius(len(reference), checkpoint, pattern_alpha)
            stages.append(
                {
                    "checkpoint": checkpoint,
                    "dimension_violations": violations,
                    "dimension_violation_frequency": violations / checkpoint,
                    "dimension_violation_probability_interval": list(violation_interval),
                    "rank_four_observed_total_variation": observed_tv,
                    "rank_four_confidence_radius": radius,
                    "rank_four_true_tv_interval": [
                        max(0.0, observed_tv - radius), min(1.0, observed_tv + radius)
                    ],
                    "dimension_stage_alpha": dimension_alpha,
                    "pattern_stage_alpha": pattern_alpha,
                }
            )
            previous = checkpoint
        rows.append({"model": name, "stages": stages})
    final = {row["model"]: row["stages"][-1] for row in rows}
    return {
        "program": "MF-STAT-001",
        "protocol": PROTOCOL,
        "rows": rows,
        "gates": {
            "target_no_observed_rank_six_violation": final["minkowski_1p1"]["dimension_violations"] == 0,
            "target_rank_four_tv_upper_below_0p06": final["minkowski_1p1"]["rank_four_true_tv_interval"][1] < 0.06,
            "three_symmetric_rank_four_tv_lower_positive": final["three_symmetric_permuton"]["rank_four_true_tv_interval"][0] > 0,
            "decorated_rank_four_tv_lower_above_0p4": final["decorated_layer"]["rank_four_true_tv_interval"][0] > 0.4,
            "three_dimensional_rank_six_violation_lower_positive": final["product_order_3d"]["dimension_violation_probability_interval"][0] > 0,
        },
        "coverage_scope": (
            "simultaneous over all preregistered checkpoints for the two allocated "
            "families; dimension bounds concern rank six only and cannot prove the "
            "universal all-rank premise"
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
