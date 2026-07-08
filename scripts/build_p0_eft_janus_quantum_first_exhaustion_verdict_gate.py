from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_quantum_first_alpha_spectrum_gate import (
    build_payload as build_alpha_payload,
)
from scripts.build_p0_eft_janus_quantum_first_boundary_mass_operator_no_go_gate import (
    build_payload as build_mass_payload,
)
from scripts.build_p0_eft_janus_quantum_first_classical_limit_gate import (
    build_payload as build_limit_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_quantum_first_exhaustion_verdict_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_quantum_first_exhaustion_verdict_gate.md"


def build_payload() -> dict[str, Any]:
    alpha = build_alpha_payload()
    limit = build_limit_payload()
    mass = build_mass_payload()
    exhausted = all(mass["routes_exhausted"].values())
    no_fit = (
        alpha["predictive_alpha_spectrum_ready"]
        and limit["no_fit_classical_janus_ready"]
        and mass["boundary_mass_operator_derived"]
    )
    return {
        "status": "janus-quantum-first-exhaustion-verdict-gate",
        "routes_exhausted": mass["routes_exhausted"],
        "all_quantum_first_routes_audited": exhausted,
        "conditional_alpha_spectrum_ready": alpha["conditional_alpha_spectrum_ready"],
        "conditional_classical_limit_ready": limit["conditional_classical_limit_ready"],
        "boundary_mass_operator_derived": mass["boundary_mass_operator_derived"],
        "primitive_sector_law_derived": mass["primitive_sector_law_derived"],
        "no_fit_alpha_generated": no_fit,
        "final_branch_status": "exhausted_conditional_spectrum_no_alpha_prediction",
        "what_quantum_first_really_adds": [
            "discrete labels are natural once CP1 is accepted",
            "prequantization is clean and non-phenomenological",
            "classical Janus can be recovered conditionally from alpha_j",
        ],
        "what_it_cannot_do_yet": [
            "derive the boundary mass operator",
            "derive the dimensionful energy unit",
            "select the primitive nonzero sector",
            "predict alpha without state input",
        ],
        "only_remaining_non_rustine_exits": [
            "derive a boundary Hamiltonian from a quantum action with time generator",
            "derive a Janus boundary TQFT with level and nonzero Hamiltonian/charge map",
            "derive a quantum area-to-mass law from the throat geometry",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Quantum-First Exhaustion Verdict Gate",
        "",
        f"All routes audited: `{payload['all_quantum_first_routes_audited']}`",
        f"Conditional alpha spectrum ready: `{payload['conditional_alpha_spectrum_ready']}`",
        f"Conditional classical limit ready: `{payload['conditional_classical_limit_ready']}`",
        f"Boundary mass operator derived: `{payload['boundary_mass_operator_derived']}`",
        f"No-fit alpha generated: `{payload['no_fit_alpha_generated']}`",
        f"Final branch status: `{payload['final_branch_status']}`",
        "",
        "## What Quantum-First Adds",
        *[f"- `{item}`" for item in payload["what_quantum_first_really_adds"]],
        "",
        "## What It Cannot Do Yet",
        *[f"- `{item}`" for item in payload["what_it_cannot_do_yet"]],
        "",
        "## Only Remaining Non-Rustine Exits",
        *[f"- `{item}`" for item in payload["only_remaining_non_rustine_exits"]],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
