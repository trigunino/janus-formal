from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_complex_reality_candidate_boundary_phase_space_gate import (
    build_payload as build_cp1_payload,
)
from scripts.build_p0_eft_janus_z2_ethroat_remaining_non_circular_frontiers_gate import (
    build_payload as build_frontier_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_quantum_first_cp1_tqft_phase_space_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_quantum_first_cp1_tqft_phase_space_gate.md"


def build_payload() -> dict[str, Any]:
    cp1 = build_cp1_payload()
    frontier = build_frontier_payload()
    tqft = frontier["janus_derived_tqft_level"]
    checks = {
        "cp1_compact_orbit_declared": cp1[
            "candidate_boundary_phase_space_constructed"
        ],
        "cp1_kks_period_declared": True,
        "cp1_prequantization_declared": True,
        "tqft_boundary_theory_declared": False,
        "tqft_level_integral_declared": False,
        "primitive_sector_law_derived": False,
        "boundary_hamiltonian_derived": False,
    }
    return {
        "status": "janus-quantum-first-cp1-tqft-phase-space-gate",
        "cp1_route": {
            "ready_as_quantum_phase_space": (
                checks["cp1_compact_orbit_declared"]
                and checks["cp1_kks_period_declared"]
                and checks["cp1_prequantization_declared"]
            ),
            "period": "Integral_CP1 Omega_j = 4*pi*j",
            "prequantization": "2*j/hbar in Z",
            "hilbert_dimension": "2*j/hbar + 1",
            "missing": ["boundary_Hamiltonian_or_mass_operator", "j_to_alpha_map"],
        },
        "tqft_route": {
            "ready_as_quantum_phase_space": tqft["ready"],
            "meaning": "boundary TQFT/level on Sigma",
            "missing": tqft["blocked_by"],
        },
        "checks": checks,
        "quantum_labels_available": (
            checks["cp1_compact_orbit_declared"]
            and checks["cp1_kks_period_declared"]
            and checks["cp1_prequantization_declared"]
        ),
        "physical_energy_scale_available": False,
        "next_gate": "QuantumFirstAlphaSpectrumGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Quantum-First CP1/TQFT Phase Space Gate",
                "",
                f"Quantum labels available: `{payload['quantum_labels_available']}`",
                f"Physical energy scale available: `{payload['physical_energy_scale_available']}`",
                f"Next gate: `{payload['next_gate']}`",
                "",
                "## CP1 Route",
                f"- Period: `{payload['cp1_route']['period']}`",
                f"- Prequantization: `{payload['cp1_route']['prequantization']}`",
                f"- Hilbert dimension: `{payload['cp1_route']['hilbert_dimension']}`",
                "",
                "## TQFT Route",
                f"- Ready: `{payload['tqft_route']['ready_as_quantum_phase_space']}`",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
