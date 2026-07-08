from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_complex_reality_candidate_phase_space_matrix_gate import (
    build_payload as build_matrix_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_quantum_candidate_workbench_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_quantum_candidate_workbench_gate.md"


def build_payload() -> dict[str, Any]:
    matrix = build_matrix_payload()
    workbench = {
        "active_throat_S2": {
            "quantum_object_if_accepted": "S2 geometric KKS quantization",
            "hilbert_space_candidate": "spin-like finite sector if Omega_Sigma period is nonzero",
            "calculable_now": ["topological_support"],
            "blocked_by": ["active_Omega_Sigma_pullback", "nonzero_area_component"],
            "alpha_ready": False,
        },
        "CP1_spinor_frame_orbit": {
            "quantum_object_if_accepted": "spin-j CP1 coadjoint orbit",
            "hilbert_space_candidate": "irreducible SU(2) representation with dim = 2*j/hbar + 1",
            "calculable_now": [
                "KKS_period_4pi_j",
                "prequantization_condition_2j_over_hbar_integer",
            ],
            "blocked_by": ["Janus_PT_derives_CP1_orbit", "map_j_to_alpha_m"],
            "alpha_ready": False,
        },
        "aroundSigma_cross_compact_phase": {
            "quantum_object_if_accepted": "action-angle torus",
            "hilbert_space_candidate": "integer action/holonomy sectors",
            "calculable_now": ["aroundSigma_Z2_one_cycle"],
            "blocked_by": ["compact_phase_derived", "normalized_action_period", "alpha_map"],
            "alpha_ready": False,
        },
    }
    ranked = [
        "CP1_spinor_frame_orbit",
        "active_throat_S2",
        "aroundSigma_cross_compact_phase",
    ]
    return {
        "status": "janus-complex-reality-quantum-candidate-workbench-gate",
        "source_matrix_ready": matrix["matrix_ready"],
        "workbench": workbench,
        "ranked_for_quantum_followup": ranked,
        "best_current_quantum_candidate": ranked[0],
        "any_candidate_alpha_ready": any(item["alpha_ready"] for item in workbench.values()),
        "interpretation": (
            "Putting the three candidates into the quantum workbench does not "
            "fix alpha. It ranks CP1 as the cleanest quantizable candidate, "
            "active S2 as the cleanest geometric route, and aroundSigma as "
            "blocked until a compact phase is derived."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Quantum Candidate Workbench Gate",
                "",
                f"Best current quantum candidate: `{payload['best_current_quantum_candidate']}`",
                f"Any candidate alpha-ready: `{payload['any_candidate_alpha_ready']}`",
                "",
                payload["interpretation"],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
