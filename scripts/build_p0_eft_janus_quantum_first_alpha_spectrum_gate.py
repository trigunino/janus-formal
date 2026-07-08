from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_quantum_first_cp1_tqft_phase_space_gate import (
    build_payload as build_phase_space_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_quantum_first_alpha_spectrum_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_quantum_first_alpha_spectrum_gate.md"


def build_payload() -> dict[str, Any]:
    phase = build_phase_space_payload()
    checks = {
        "quantum_labels_available": phase["quantum_labels_available"],
        "boundary_mass_operator_derived": False,
        "alpha_mass_map_declared": True,
        "alpha_spectrum_conditional": True,
        "alpha_spectrum_numerical": False,
    }
    conditional_ready = (
        checks["quantum_labels_available"]
        and checks["alpha_mass_map_declared"]
        and checks["alpha_spectrum_conditional"]
    )
    predictive_ready = conditional_ready and checks["boundary_mass_operator_derived"]
    return {
        "status": "janus-quantum-first-alpha-spectrum-gate",
        "checks": checks,
        "conditional_alpha_spectrum_ready": conditional_ready,
        "predictive_alpha_spectrum_ready": predictive_ready,
        "conditional_spectrum": {
            "cp1": "if M_j is derived, alpha_j = -2*pi*G*M_j/c^2 with 2*j/hbar in Z",
            "tqft": "if Q_n or M_n is derived, alpha_n = -2*pi*G*M_n/c^2",
        },
        "blocked_by": [
            "boundary_mass_operator_or_energy_function_not_derived",
            "primitive_sector_selection_not_derived",
            "dimensionful_energy_unit_not_derived",
        ],
        "next_gate": "QuantumFirstClassicalLimitGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Quantum-First Alpha Spectrum Gate",
                "",
                f"Conditional alpha spectrum ready: `{payload['conditional_alpha_spectrum_ready']}`",
                f"Predictive alpha spectrum ready: `{payload['predictive_alpha_spectrum_ready']}`",
                f"Next gate: `{payload['next_gate']}`",
                "",
                "## Conditional Spectrum",
                f"- CP1: `{payload['conditional_spectrum']['cp1']}`",
                f"- TQFT: `{payload['conditional_spectrum']['tqft']}`",
                "",
                "## Blocked By",
                *[f"- `{item}`" for item in payload["blocked_by"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
