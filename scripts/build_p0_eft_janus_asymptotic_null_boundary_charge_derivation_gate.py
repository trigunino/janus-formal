from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_asymptotic_null_boundary_candidate_matrix_gate import (
    build_payload as build_matrix_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_asymptotic_null_boundary_charge_derivation_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_asymptotic_null_boundary_charge_derivation_gate.md"


def build_payload() -> dict[str, Any]:
    matrix = build_matrix_payload()
    route_checks = {
        "BMS": {
            "asymptotic_symmetry_algebra_derived": False,
            "surface_charge_formula_available": True,
            "time_translation_generator_selected": False,
            "bondi_mass_charge_derived_for_Janus": False,
            "blocks_on": ["Janus_not_promoted_to_asymptotically_flat_scri", "Bondi_frame_or_cut_missing"],
        },
        "Newman_Penrose": {
            "np_null_tetrad_formalism_available": True,
            "np_charges_asymptotic_available": True,
            "np_charge_mapped_to_M_bridge": False,
            "blocks_on": ["asymptotic_or_null_tetrad_boundary_not_active", "mass_aspect_map_missing"],
        },
        "covariant_phase_space_null_boundary": {
            "formalism_available": True,
            "boundary_conditions_declared_for_Janus": False,
            "integrable_hamiltonian_derived": False,
            "time_generator_normalized": False,
            "blocks_on": ["boundary_conditions_missing", "null_generator_normalization_missing", "reference_missing"],
        },
    }
    return {
        "status": "janus-asymptotic-null-boundary-charge-derivation-gate",
        "candidate_matrix": matrix,
        "route_checks": route_checks,
        "boundary_mass_charge_derived": False,
        "M_bridge_charge_available": False,
        "key_result": (
            "The literature supplies charge technology, not a Janus charge. "
            "The missing Janus-specific input is a promoted null/asymptotic boundary "
            "with boundary conditions, time generator and integrable charge."
        ),
        "next_gate": "AsymptoticNullBoundaryChargesAlphaBridgeGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Asymptotic/Null Boundary Charge Derivation Gate",
        "",
        f"Boundary mass charge derived: `{payload['boundary_mass_charge_derived']}`",
        f"M_bridge charge available: `{payload['M_bridge_charge_available']}`",
        "",
        payload["key_result"],
        "",
        "## Route blockers",
    ]
    for key, item in payload["route_checks"].items():
        lines.append(f"- `{key}`: `{item['blocks_on']}`")
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
