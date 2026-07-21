"""MF-MAN-019: asymptotic decay of the largest relational-twin fraction."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_ensemble_moment_adversary import antichain, total_order
    from scripts.audit_program_m_ensemble_separation import (
        accepts as moment_gate_accepts,
        ensemble_statistics,
        minkowski_order,
    )
    from scripts.audit_program_m_exact_twins import largest_twin_class
    from scripts.audit_program_m_height_growth import PROTOCOL as HEIGHT_PROTOCOL, order_height
    from scripts.audit_program_m_infinite_layer_adversary import infinite_layer_order
except ModuleNotFoundError:
    from audit_program_m_ensemble_moment_adversary import antichain, total_order
    from audit_program_m_ensemble_separation import (
        accepts as moment_gate_accepts,
        ensemble_statistics,
        minkowski_order,
    )
    from audit_program_m_exact_twins import largest_twin_class
    from audit_program_m_height_growth import PROTOCOL as HEIGHT_PROTOCOL, order_height
    from audit_program_m_infinite_layer_adversary import infinite_layer_order


PROTOCOL = {
    "protocol_id": "MF-MAN-019-v1",
    "base_seed": 2026071807,
    "validation_sizes": [384, 768, 1536, 3072],
    "replicates_per_model": 64,
    "largest_twin_fraction_ratio_max_exclusive": 0.5,
    "derivation": (
        "fixed between decay 1/8 for a bounded twin multiplicity over an "
        "eightfold size increase and ratio 1 for a macroscopic atomic class"
    ),
    "frozen_moment_gate": HEIGHT_PROTOCOL["frozen_moment_gate"],
    "frozen_height_ratio_min": HEIGHT_PROTOCOL["height_ratio_min"],
}


GENERATORS = {
    "minkowski_1p1": minkowski_order,
    "infinite_layer": infinite_layer_order,
    "total_order": total_order,
    "antichain": antichain,
}


def run_audit() -> dict[str, object]:
    rows = []
    sizes = PROTOCOL["validation_sizes"]
    for model_index, (model, generator) in enumerate(GENERATORS.items()):
        samples = []
        for replicate in range(int(PROTOCOL["replicates_per_model"])):
            heights = []
            twin_fractions = []
            moment_acceptance = []
            for size_index, size in enumerate(sizes):
                seed = (
                    int(PROTOCOL["base_seed"])
                    + 100_000_000 * model_index
                    + 100_000 * size_index
                    + replicate
                )
                order = generator(size, np.random.default_rng(seed))
                heights.append(order_height(order))
                twin_fractions.append(largest_twin_class(order) / size)
                moment_acceptance.append(
                    moment_gate_accepts(
                        ensemble_statistics(order), PROTOCOL["frozen_moment_gate"]
                    )
                )
            height_ratio = heights[-1] / heights[0]
            twin_ratio = twin_fractions[-1] / twin_fractions[0]
            prior_accepted = (
                all(moment_acceptance)
                and height_ratio > PROTOCOL["frozen_height_ratio_min"]
            )
            twin_accepted = (
                twin_ratio
                < PROTOCOL["largest_twin_fraction_ratio_max_exclusive"]
            )
            samples.append(
                {
                    "heights": heights,
                    "height_ratio": height_ratio,
                    "largest_twin_fractions": twin_fractions,
                    "twin_fraction_ratio": twin_ratio,
                    "prior_accepted": prior_accepted,
                    "twin_accepted": twin_accepted,
                    "combined_accepted": prior_accepted and twin_accepted,
                }
            )
        rows.append(
            {
                "model": model,
                "replicates": len(samples),
                "mean_largest_twin_fractions": np.mean(
                    np.array([sample["largest_twin_fractions"] for sample in samples]),
                    axis=0,
                ).tolist(),
                "mean_twin_fraction_ratio": float(
                    np.mean([sample["twin_fraction_ratio"] for sample in samples])
                ),
                "prior_acceptance_rate": float(
                    np.mean([sample["prior_accepted"] for sample in samples])
                ),
                "combined_acceptance_rate": float(
                    np.mean([sample["combined_accepted"] for sample in samples])
                ),
            }
        )
    by_model = {row["model"]: row for row in rows}
    return {
        "program": "MF-MAN-019",
        "protocol": PROTOCOL,
        "rows": rows,
        "gates": {
            "target_combined_acceptance_at_least_0p90":
                by_model["minkowski_1p1"]["combined_acceptance_rate"] >= 0.90,
            "infinite_layer_combined_acceptance_zero":
                by_model["infinite_layer"]["combined_acceptance_rate"] == 0.0,
            "total_order_combined_acceptance_zero":
                by_model["total_order"]["combined_acceptance_rate"] == 0.0,
            "antichain_combined_acceptance_zero":
                by_model["antichain"]["combined_acceptance_rate"] == 0.0,
        },
        "scope": (
            "necessary diffuseness diagnostic for exact relational types; "
            "does not exclude approximate twins or prove a continuum"
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

