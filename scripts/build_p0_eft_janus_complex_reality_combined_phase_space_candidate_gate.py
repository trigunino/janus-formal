from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_complex_reality_quantum_candidate_workbench_gate import (
    build_payload as build_workbench_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_combined_phase_space_candidate_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_combined_phase_space_candidate_gate.md"


def build_payload() -> dict[str, Any]:
    workbench = build_workbench_payload()
    combined = {
        "name": "S2_throat_CP1_fiber_aroundSigma_holonomy",
        "base_support": "active_throat_S2",
        "quantum_fiber": "CP1_spinor_frame_orbit",
        "global_constraint": "aroundSigma_holonomy",
        "concept": "CP1 boundary spinor/frame fiber over Sigma throat with tunnel holonomy constraint",
    }
    checks = {
        "individual_candidates_preserved": workbench["source_matrix_ready"],
        "base_support_available": True,
        "cp1_fiber_constructed_mathematically": True,
        "aroundSigma_cycle_available": True,
        "cp1_derived_from_Janus_PT": False,
        "aroundSigma_action_on_CP1_derived": False,
        "combined_KKS_period_nonzero": False,
        "sector_selection_law_derived": False,
        "alpha_map_derived": False,
    }
    coherent_candidate = all(
        checks[key]
        for key in [
            "individual_candidates_preserved",
            "base_support_available",
            "cp1_fiber_constructed_mathematically",
            "aroundSigma_cycle_available",
        ]
    )
    physically_closed = coherent_candidate and all(
        checks[key]
        for key in [
            "cp1_derived_from_Janus_PT",
            "aroundSigma_action_on_CP1_derived",
            "combined_KKS_period_nonzero",
            "sector_selection_law_derived",
            "alpha_map_derived",
        ]
    )
    return {
        "status": "janus-complex-reality-combined-phase-space-candidate-gate",
        "combined_candidate": combined,
        "checks": checks,
        "combined_candidate_coherent": coherent_candidate,
        "combined_candidate_physically_closed": physically_closed,
        "alpha_generated_now": False,
        "what_it_combines": [
            "S2 support from Sigma",
            "CP1 quantizable fiber",
            "aroundSigma holonomy constraint",
        ],
        "still_missing": [key for key, ok in checks.items() if not ok],
        "next_gate": "ComplexRealityAroundSigmaCP1HolonomyActionGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Combined Phase-Space Candidate Gate",
                "",
                f"Combined candidate coherent: `{payload['combined_candidate_coherent']}`",
                f"Physically closed: `{payload['combined_candidate_physically_closed']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                f"Next gate: `{payload['next_gate']}`",
                "",
                "## Combines",
                "",
                *[f"- `{item}`" for item in payload["what_it_combines"]],
                "",
                "## Still Missing",
                "",
                *[f"- `{item}`" for item in payload["still_missing"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
