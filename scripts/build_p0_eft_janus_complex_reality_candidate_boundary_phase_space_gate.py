from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_candidate_boundary_phase_space_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_candidate_boundary_phase_space_gate.md"


def build_payload() -> dict[str, Any]:
    candidate = {
        "name": "CP1_boundary_spinor_frame_orbit",
        "interpretation": (
            "A compact boundary spinor/frame orbit attached to Sigma. "
            "Mathematically it gives CP1 ~= S2, a closed two-cycle carrying "
            "the standard SU(2)/KKS symplectic form."
        ),
        "phase_space": {
            "support": "Sigma throat boundary",
            "compact_fiber": "CP1 ~= SU(2)/U(1) ~= S2",
            "coordinate_model": "normalized complex spinor xi modulo phase",
            "kks_form": "Omega_j = j*sin(theta)*dtheta^dphi",
            "closed_two_cycle": "CP1",
            "period": "Integral_CP1 Omega_j = 4*pi*j",
            "prequantization": "Integral_CP1 Omega_j/(2*pi*hbar) = 2*j/hbar in Z",
        },
    }
    checks = {
        "compact_boundary_phase_space_constructed": True,
        "closed_two_cycle_constructed": True,
        "KKS_form_declared": True,
        "symbolic_period_nonzero_if_j_nonzero": True,
        "prequantization_condition_declared": True,
        "source_derived_from_Janus_PT": False,
        "map_from_spin_orbit_j_to_alpha_m_derived": False,
        "primitive_nonzero_sector_selected": False,
    }
    constructed = all(
        checks[key]
        for key in [
            "compact_boundary_phase_space_constructed",
            "closed_two_cycle_constructed",
            "KKS_form_declared",
            "symbolic_period_nonzero_if_j_nonzero",
            "prequantization_condition_declared",
        ]
    )
    physically_accepted = constructed and all(
        checks[key]
        for key in [
            "source_derived_from_Janus_PT",
            "map_from_spin_orbit_j_to_alpha_m_derived",
            "primitive_nonzero_sector_selected",
        ]
    )
    return {
        "status": "janus-complex-reality-candidate-boundary-phase-space-gate",
        "candidate": candidate,
        "checks": checks,
        "candidate_boundary_phase_space_constructed": constructed,
        "candidate_boundary_phase_space_physically_accepted": physically_accepted,
        "alpha_generated_now": False,
        "what_this_proves": [
            "a closed two-cycle with nonzero symbolic KKS period can be constructed",
            "prequantization would quantize the orbit label j",
        ],
        "what_this_does_not_prove": [
            "that Janus/PT requires this CP1 boundary orbit",
            "that j maps to alpha_m",
            "that the primitive nonzero sector is selected",
        ],
        "verdict": (
            "This is a valid mathematical candidate for the missing boundary "
            "phase space. It is not yet a Janus-derived no-fit state law."
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
                "# Janus Complex Reality Candidate Boundary Phase Space Gate",
                "",
                f"Constructed: `{payload['candidate_boundary_phase_space_constructed']}`",
                f"Physically accepted: `{payload['candidate_boundary_phase_space_physically_accepted']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                "",
                payload["verdict"],
                "",
                "## Candidate",
                "",
                *[
                    f"- `{key}`: `{value}`"
                    for key, value in payload["candidate"]["phase_space"].items()
                ],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
