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
from scripts.build_p0_eft_janus_z2_sigma_spinor_projection_readiness_gate import (
    build_payload as build_spinor_projection_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_noncentral_spin_lift_search_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_noncentral_spin_lift_search_gate.md"


def build_payload() -> dict[str, Any]:
    around = build_around_sigma_payload()
    spinor = build_spinor_projection_payload()
    candidate_lifts = {
        "central_minus_identity": {
            "spin_lift": "-I in SU(2)",
            "projects_to_CP1": "identity",
            "sector_selection_power": "none",
            "admissible": True,
        },
        "noncentral_pi_rotation": {
            "spin_lift": "exp(i*pi*sigma_axis/2)",
            "projects_to_CP1": "SO(3) pi-rotation",
            "sector_selection_power": "possible",
            "admissible": False,
            "missing": "axis/normal frame holonomy derived from resolved tunnel",
        },
        "generic_U1_phase": {
            "spin_lift": "exp(i*theta) scalar phase",
            "projects_to_CP1": "identity",
            "sector_selection_power": "phase_only_not_CP1_orbit_selection",
            "admissible": False,
            "missing": "physical compact phase law and normalization",
        },
    }
    checks = {
        "aroundSigma_Z2_cycle_closed": around["around_sigma_z2_transport_closed"],
        "spinor_projection_readiness_declared": spinor[
            "spinor_projection_readiness_ledger_declared"
        ],
        "resolved_tunnel_Pin_lift_ready": spinor["readiness"][
            "resolved_tunnel_Pin_lift_ready"
        ],
        "global_spinor_projection_ready": spinor["spinor_projection_readiness_ready"],
        "noncentral_lift_forced_by_geometry": False,
        "noncentral_lift_axis_derived": False,
    }
    search_complete = checks["aroundSigma_Z2_cycle_closed"] and checks[
        "spinor_projection_readiness_declared"
    ]
    noncentral_lift_derived = search_complete and all(
        checks[key]
        for key in [
            "resolved_tunnel_Pin_lift_ready",
            "global_spinor_projection_ready",
            "noncentral_lift_forced_by_geometry",
            "noncentral_lift_axis_derived",
        ]
    )
    return {
        "status": "janus-complex-reality-noncentral-spin-lift-search-gate",
        "candidate_lifts": candidate_lifts,
        "checks": checks,
        "search_complete": search_complete,
        "noncentral_spin_lift_derived": noncentral_lift_derived,
        "verdict": (
            "The central spin lift is admissible but acts trivially on CP1. "
            "A useful noncentral pi-rotation is possible in principle, but the "
            "resolved tunnel Pin/spin geometry does not currently force it or "
            "derive its axis."
        ),
        "still_missing": [key for key, ok in checks.items() if not ok],
        "next_gate": "ComplexRealityCombinedBranchVerdictGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Noncentral Spin Lift Search Gate",
                "",
                f"Search complete: `{payload['search_complete']}`",
                f"Noncentral spin lift derived: `{payload['noncentral_spin_lift_derived']}`",
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
