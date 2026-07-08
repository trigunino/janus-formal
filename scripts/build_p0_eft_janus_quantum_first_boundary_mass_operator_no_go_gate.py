from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_quantum_first_cp1_tqft_phase_space_gate import (
    build_payload as build_phase_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_quantum_first_boundary_mass_operator_no_go_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_quantum_first_boundary_mass_operator_no_go_gate.md"


def build_payload() -> dict[str, Any]:
    phase = build_phase_payload()
    cp1_attempts = {
        "moment_map_Ji": {
            "available": phase["quantum_labels_available"],
            "candidate_mass": "M_jm = epsilon_unit*m with m=-j,...,+j",
            "fails_without": ["choice_of_time_generator", "dimensionful_epsilon_unit"],
            "derived_mass_operator": False,
        },
        "casimir_J2": {
            "available": phase["quantum_labels_available"],
            "candidate_mass": "M_j = lambda_unit*j*(j+hbar)",
            "fails_without": ["dimensionful_lambda_unit", "physical_map_J2_to_boundary_energy"],
            "derived_mass_operator": False,
        },
        "area_gap_like": {
            "available": phase["quantum_labels_available"],
            "candidate_mass": "A_j proportional sqrt(j*(j+hbar)); M still needs energy/length map",
            "fails_without": ["Janus_area_to_mass_law", "primitive_sector_selection"],
            "derived_mass_operator": False,
        },
    }
    tqft_attempts = {
        "chern_simons_closed_boundary": {
            "available": False,
            "candidate_labels": "level k, representation labels, flux sectors",
            "hamiltonian_status": "topological_constraint_or_zero_on_closed_boundary",
            "fails_without": ["boundary_time_generator", "nonzero_boundary_Hamiltonian", "level_from_Janus_action"],
            "derived_mass_operator": False,
        },
        "tqft_partition_function": {
            "available": False,
            "candidate_labels": "Z_TQFT(Sigma,k)",
            "fails_without": ["Janus_derived_TQFT", "level_k", "energy_from_logZ_temperature_or_time"],
            "derived_mass_operator": False,
        },
    }
    return {
        "status": "janus-quantum-first-boundary-mass-operator-no-go-gate",
        "cp1_attempts": cp1_attempts,
        "tqft_attempts": tqft_attempts,
        "boundary_mass_operator_derived": False,
        "dimensionful_energy_unit_derived": False,
        "primitive_sector_law_derived": False,
        "no_go_statement": (
            "CP1/prequantization discretizes labels but does not select a time "
            "generator or energy unit. A closed TQFT/CS boundary supplies sectors "
            "but no nonzero Hamiltonian unless a boundary time generator or action "
            "normalization is derived. Therefore alpha remains conditional."
        ),
        "routes_exhausted": {
            "cp1_moment_map": True,
            "cp1_casimir": True,
            "cp1_area_gap_like": True,
            "closed_tqft_hamiltonian": True,
            "prequantization_only": True,
        },
        "next_gate": "QuantumFirstExhaustionVerdictGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Quantum-First Boundary Mass Operator No-Go Gate",
        "",
        f"Boundary mass operator derived: `{payload['boundary_mass_operator_derived']}`",
        f"Dimensionful energy unit derived: `{payload['dimensionful_energy_unit_derived']}`",
        f"Primitive sector law derived: `{payload['primitive_sector_law_derived']}`",
        "",
        payload["no_go_statement"],
        "",
        "## CP1 Attempts",
    ]
    for key, item in payload["cp1_attempts"].items():
        lines.append(f"- `{key}`: derived=`{item['derived_mass_operator']}`; fails_without=`{item['fails_without']}`")
    lines.extend(["", "## TQFT Attempts"])
    for key, item in payload["tqft_attempts"].items():
        lines.append(f"- `{key}`: derived=`{item['derived_mass_operator']}`; fails_without=`{item['fails_without']}`")
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
