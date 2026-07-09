from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_asymptotic_null_boundary_candidate_matrix_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_asymptotic_null_boundary_candidate_matrix_gate.md"


def build_payload() -> dict[str, Any]:
    candidates = {
        "null_infinity_BMS": {
            "can_define_energy": True,
            "energy_object": "Bondi mass / supertranslation charge",
            "requires": [
                "asymptotically_flat_null_infinity",
                "Bondi_frame_or_cut",
                "time_translation_supertranslation",
                "flux_balance",
            ],
            "available_in_current_Janus_core": False,
            "reason": "current active Janus core is compact/projective/Sigma-throat, not an asymptotically flat scri construction",
        },
        "internal_null_PT_bridge": {
            "can_define_energy": "conditional",
            "energy_object": "null boundary Hamiltonian or Brown-York-like null charge",
            "requires": [
                "null_boundary_structure",
                "normalization_of_null_generator",
                "boundary_conditions",
                "integrable_charge",
                "reference_or_time_generator",
            ],
            "available_in_current_Janus_core": False,
            "reason": "null/PT bridge exists as a branch, but normalization/time generator and state charge remain unselected",
        },
        "finite_Sigma_throat": {
            "can_define_energy": "not_by_BMS",
            "energy_object": "quasilocal charge if boundary action/reference is supplied",
            "requires": [
                "boundary_Hamiltonian",
                "reference_subtraction",
                "active_embedding_or_boundary_state",
            ],
            "available_in_current_Janus_core": False,
            "reason": "finite Sigma is not an asymptotic symmetry boundary; it returns to prior Brown-York/Souriau blockers",
        },
    }
    return {
        "status": "janus-asymptotic-null-boundary-candidate-matrix-gate",
        "candidates": candidates,
        "best_route": "internal_null_PT_bridge_if_promoted_to_real_null_boundary_with_integrable_charge",
        "bms_route_ready": False,
        "internal_null_charge_route_ready": False,
        "finite_sigma_bms_route_ready": False,
        "next_gate": "AsymptoticNullBoundaryChargesChargeDerivationGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Asymptotic/Null Boundary Candidate Matrix Gate",
        "",
        f"Best route: `{payload['best_route']}`",
        f"BMS route ready: `{payload['bms_route_ready']}`",
        f"Internal null charge route ready: `{payload['internal_null_charge_route_ready']}`",
        "",
        "## Candidates",
    ]
    for key, item in payload["candidates"].items():
        lines.append(f"- `{key}`: energy=`{item['energy_object']}`; available=`{item['available_in_current_Janus_core']}`; {item['reason']}")
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
