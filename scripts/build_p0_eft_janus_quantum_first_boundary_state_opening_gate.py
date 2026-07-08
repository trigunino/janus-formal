from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_quantum_first_boundary_state_opening_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_quantum_first_boundary_state_opening_gate.md"
DOC_PATH = Path("docs/janus_quantum_first_boundary_state.md")


def build_payload() -> dict[str, Any]:
    return {
        "status": "janus-quantum-first-boundary-state-opening-gate",
        "conceptual_branch": "janus_quantum_first_boundary_state",
        "program": [
            "Quantum boundary state",
            "CP1/TQFT phase space",
            "prequantization",
            "alpha spectrum",
            "classical Janus limit",
        ],
        "allowed_postulate": (
            "Boundary quantum state is primary; Sigma/tunnel geometry is recovered "
            "as a classical or large-quantum-number limit."
        ),
        "forbidden_claims": [
            "alpha_numerically_fixed_now",
            "paper_Janus_replaced_now",
            "observations_matched_now",
            "CP1_or_TQFT_selected_without_state_law",
        ],
        "branch_opened": True,
        "next_gate": "QuantumFirstCP1TQFTPhaseSpaceGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Quantum-First Boundary State Opening Gate",
                "",
                f"Branch opened: `{payload['branch_opened']}`",
                f"Conceptual branch: `{payload['conceptual_branch']}`",
                f"Next gate: `{payload['next_gate']}`",
                "",
                payload["allowed_postulate"],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
