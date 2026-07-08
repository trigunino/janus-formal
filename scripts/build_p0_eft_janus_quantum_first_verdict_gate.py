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
JSON_PATH = REPORTS / "p0_eft_janus_quantum_first_verdict_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_quantum_first_verdict_gate.md"


def build_payload() -> dict[str, Any]:
    alpha = build_alpha_payload()
    limit = build_limit_payload()
    mass = build_mass_payload()
    no_fit_closed = (
        alpha["predictive_alpha_spectrum_ready"]
        and limit["no_fit_classical_janus_ready"]
        and mass["boundary_mass_operator_derived"]
    )
    return {
        "status": "janus-quantum-first-verdict-gate",
        "conditional_alpha_spectrum_ready": alpha["conditional_alpha_spectrum_ready"],
        "conditional_classical_limit_ready": limit["conditional_classical_limit_ready"],
        "boundary_mass_operator_derived": mass["boundary_mass_operator_derived"],
        "primitive_sector_law_derived": mass["primitive_sector_law_derived"],
        "boundary_mass_operator_routes_exhausted": mass["routes_exhausted"],
        "no_fit_alpha_generated": no_fit_closed,
        "branch_status": (
            "conditional_quantum_spectrum_only"
            if not no_fit_closed
            else "no_fit_quantum_first_alpha_law"
        ),
        "hard_blocker": (
            "Quantum-first improves the structure: labels can be discrete and the "
            "classical Janus limit can be stated conditionally. It still needs a "
            "derived boundary Hamiltonian/mass operator and primitive sector law "
            "before alpha is predicted."
        ),
        "next_non_rustine_targets": [
            "derive_boundary_mass_operator_from_quantum_state",
            "derive_primitive_sector_selection_law",
            "derive_dimensionful_energy_unit_without_H0_or_observation",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Quantum-First Verdict Gate",
                "",
                f"Branch status: `{payload['branch_status']}`",
                f"Conditional alpha spectrum ready: `{payload['conditional_alpha_spectrum_ready']}`",
                f"Conditional classical limit ready: `{payload['conditional_classical_limit_ready']}`",
                f"No-fit alpha generated: `{payload['no_fit_alpha_generated']}`",
                "",
                payload["hard_blocker"],
                "",
                "## Next Non-Rustine Targets",
                *[f"- `{item}`" for item in payload["next_non_rustine_targets"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
