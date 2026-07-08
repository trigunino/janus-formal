from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_complex_reality_active_embedding_or_compact_phase_gate import (
    build_payload as build_exit_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_two_exit_evaluation_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_two_exit_evaluation_gate.md"


def build_payload() -> dict[str, Any]:
    exits = build_exit_payload()
    active = exits["active_embedding_route"]
    phase = exits["compact_phase_route"]
    evaluation = {
        "active_embedding_on_S2": {
            "status": "preferred_direct_route",
            "why": (
                "Uses the already identified throat angular S2. It does not "
                "need new topology, only the active embedding and the actual "
                "Omega_Sigma pullback density."
            ),
            "non_rustine_if": [
                "active_embedding_values_are_derived_from_Z2_tunnel_geometry",
                "boundary_variations_are_physical_after_gauge_quotient",
                "Omega_Sigma_has_nonzero_S2_area_component",
            ],
            "currently_missing": [
                key for key, ok in active["checks"].items() if not ok
            ],
            "risk": "may evaluate to zero even after embedding is supplied",
        },
        "aroundSigma_cross_compact_phase": {
            "status": "higher_risk_topological_route",
            "why": (
                "Turns the known aroundSigma Z2 one-cycle into a two-cycle by "
                "pairing it with a compact phase/fiber direction. This can "
                "produce an S1 x S1 torus, but only if the phase is derived "
                "from Janus/PT/Souriau data, not postulated."
            ),
            "non_rustine_if": [
                "compact_phase_is_derived_from_complex_reality_or_PT_holonomy",
                "phase_period_is_normalized_by_source_law",
                "KKS_cross_pairing_between_aroundSigma_and_phase_is_nonzero",
            ],
            "currently_missing": [
                key for key, ok in phase["checks"].items() if not ok
            ],
            "risk": "most likely requires an extra boundary phase-space law",
        },
    }
    topology_answer = {
        "short_answer": (
            "The question is not only which topology gives a closed two-cycle. "
            "It is which physical boundary phase space gives a closed two-cycle "
            "with nonzero pullback of Omega_Sigma."
        ),
        "sufficient_patterns": [
            "S2_throat with nonzero Omega_Sigma angular area component",
            "aroundSigma_S1 x compact_phase_S1 with nonzero KKS cross term",
            "coadjoint_orbit_S2 only if it is actively mapped to Sigma boundary data",
        ],
        "insufficient_patterns": [
            "aroundSigma alone, because it is a one-cycle",
            "S2 topology alone, if Omega_Sigma pullback vanishes",
            "finite coadjoint orbit cycle alone, if not connected to Sigma boundary",
        ],
    }
    return {
        "status": "janus-complex-reality-two-exit-evaluation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "evaluation": evaluation,
        "topology_answer": topology_answer,
        "recommended_order": [
            "try_active_embedding_on_S2_first",
            "try_compact_phase_route_only_if_active_S2_pullback_is_zero_or_unavailable",
        ],
        "any_exit_ready_now": exits["nonzero_KKS_boundary_period_route_ready"],
        "alpha_generated_now": False,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Two Exit Evaluation Gate",
                "",
                f"Any exit ready now: `{payload['any_exit_ready_now']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                "",
                payload["topology_answer"]["short_answer"],
                "",
                "## Recommended Order",
                "",
                *[f"- `{item}`" for item in payload["recommended_order"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
