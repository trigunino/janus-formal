from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_around_sigma_z2_cycle_transport_gate import (
    build_payload as build_around_sigma_payload,
)
from scripts.build_p0_eft_janus_complex_reality_cp1_from_janus_pt_gate import (
    build_payload as build_cp1_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_around_sigma_cp1_holonomy_action_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_around_sigma_cp1_holonomy_action_gate.md"


def build_payload() -> dict[str, Any]:
    cp1 = build_cp1_payload()
    around = build_around_sigma_payload()
    actions = {
        "central_spin_lift_minus_identity": {
            "action_on_spinor": "psi -> -psi",
            "action_on_CP1": "trivial",
            "can_select_sector": False,
        },
        "noncentral_projective_pi_rotation": {
            "action_on_spinor": "psi -> U_pi psi with U_pi^2=-I",
            "action_on_CP1": "nontrivial SO(3) pi-rotation",
            "can_select_sector": True,
            "requires_derivation": "specific Pin/spin holonomy around aroundSigma",
        },
    }
    checks = {
        "aroundSigma_Z2_cycle_available": around["around_sigma_z2_transport_closed"],
        "cp1_mathematical_candidate_ready": cp1["cp1_mathematical_candidate_ready"],
        "cp1_derived_from_Janus_PT": cp1["cp1_derived_from_Janus_PT"],
        "spin_lift_of_aroundSigma_specified": False,
        "noncentral_projective_action_derived": False,
        "action_preserves_CP1_KKS_form": True,
    }
    holonomy_action_symbolically_classified = (
        checks["aroundSigma_Z2_cycle_available"]
        and checks["cp1_mathematical_candidate_ready"]
    )
    holonomy_action_derived = holonomy_action_symbolically_classified and all(
        checks[key]
        for key in [
            "cp1_derived_from_Janus_PT",
            "spin_lift_of_aroundSigma_specified",
            "noncentral_projective_action_derived",
        ]
    )
    return {
        "status": "janus-complex-reality-around-sigma-cp1-holonomy-action-gate",
        "actions": actions,
        "checks": checks,
        "holonomy_action_symbolically_classified": holonomy_action_symbolically_classified,
        "aroundSigma_action_on_CP1_derived": holonomy_action_derived,
        "verdict": (
            "aroundSigma can act on CP1 only after a spin/Pin lift is specified. "
            "The central lift acts trivially on CP1 and cannot select a sector. "
            "A noncentral projective pi-rotation would be useful, but it is not "
            "derived from the current Janus/PT data."
        ),
        "still_missing": [key for key, ok in checks.items() if not ok],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality aroundSigma -> CP1 Holonomy Action Gate",
                "",
                f"Symbolically classified: `{payload['holonomy_action_symbolically_classified']}`",
                f"Derived: `{payload['aroundSigma_action_on_CP1_derived']}`",
                "",
                payload["verdict"],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
