"""MF-CERT-002: dependency audit for an exact Minkowski identification claim."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def run_audit() -> dict[str, object]:
    premises = [
        {
            "id": "exchangeable_projective_poset_law",
            "status": "formal_interface",
            "evidence": "ProgramMEnsembleEmergence.lean and Janson arXiv:0902.0306",
        },
        {
            "id": "every_finite_subposet_has_dimension_at_most_two",
            "status": "open_universal_premise",
            "evidence": "MF-REP-001/003 test only bounded finite samples",
        },
        {
            "id": "compactness_to_global_two_order_representation",
            "status": "published_theorem_not_formalized",
            "evidence": "finite dimension equals supremum over finite subposets",
        },
        {
            "id": "exchangeable_random_realizer_lift",
            "status": "derived_conditional_bridge",
            "evidence": "MF-REP-004: Borel lift, finite-group averaging, compactness and ergodic extreme lift",
        },
        {
            "id": "continuous_atomless_permuton_representation",
            "status": "published_consequence_of_exchangeable_order_pair",
            "evidence": "permutation-limit representation of an exchangeable pair of total orders",
        },
        {
            "id": "exact_rank_four_poset_law_equality",
            "status": "statistical_evidence_only",
            "evidence": "MF-PAT-001/002 and MF-CERT-001 use finite calibrated samples",
        },
        {
            "id": "rank_four_forcing_inside_permuton_class",
            "status": "published_plus_executable_bridge",
            "evidence": "Chan et al. arXiv:1909.11027 and MF-PAT-003",
        },
        {
            "id": "metric_or_geometry_recovery",
            "status": "not_started_here",
            "evidence": "uniform product-order law identifies an ordered measured model, not yet a metric theorem",
        },
    ]
    blocking = {
        premise["id"]
        for premise in premises
        if premise["status"]
        in {
            "open_universal_premise",
            "missing_bridge",
            "statistical_evidence_only",
            "not_started_here",
        }
    }
    expected_blocking = {
        "every_finite_subposet_has_dimension_at_most_two",
        "exact_rank_four_poset_law_equality",
        "metric_or_geometry_recovery",
    }
    return {
        "program": "MF-CERT-002",
        "premises": premises,
        "blocking_exact_claim": sorted(blocking),
        "safe_claims": {
            "finite_statistical_certificate": True,
            "conditional_permuton_identification": True,
            "exact_unconditional_minkowski_identification": False,
            "emergent_metric_geometry": False,
        },
        "gates": {
            "all_expected_gaps_are_explicit": blocking == expected_blocking,
            "exact_claim_is_not_promoted": True,
            "metric_claim_is_not_promoted": True,
        },
        "next_research_target": (
            "upgrade bounded dimension-two evidence and rank-four agreement into "
            "asymptotic confidence sequences without claiming finite proof of exact equality"
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
