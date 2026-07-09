from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_asymptotic_null_boundary_symmetry_opening_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_asymptotic_null_boundary_symmetry_opening_gate.md"


def build_payload() -> dict[str, Any]:
    return {
        "status": "janus-asymptotic-null-boundary-symmetry-opening-gate",
        "conceptual_branch": "janus_asymptotic_null_boundary_symmetry",
        "target_blocker": "boundary_mass_energy_operator",
        "routes": ["BMS", "Newman-Penrose", "covariant_phase_space_null_boundary"],
        "bibliography_anchors": [
            "BMS group gives asymptotic symmetries and Bondi charges at null infinity",
            "Wald-Zoupas gives charges and fluxes at null infinity",
            "null boundary covariant phase space can define Hamiltonians under boundary conditions",
            "Newman-Penrose formalism is natural for null boundary structure",
        ],
        "forbidden_claims": [
            "alpha_fixed_now",
            "M_bridge_derived_without_boundary_charge",
            "internal_Sigma_treated_as_null_infinity_without_proof",
            "observations_used_as_charge_reference",
        ],
        "branch_opened": True,
        "next_gate": "AsymptoticNullBoundaryChargesCandidateMatrixGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Asymptotic/Null Boundary Symmetry Opening Gate",
                "",
                f"Branch opened: `{payload['branch_opened']}`",
                f"Target blocker: `{payload['target_blocker']}`",
                f"Next gate: `{payload['next_gate']}`",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
