from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_projected_baryon_noether_charge_input_gate import (
    build_payload as build_charge,
)
from scripts.build_p0_eft_janus_z2_sigma_spatial_volume_projective_slice_gate import (
    build_payload as build_volume,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_solution_to_embedding_curvature_branch_gate import (
    build_payload as build_rsigma_to_curvature,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_state_prerequisite_derivability_audit_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_state_prerequisite_derivability_audit_gate.json"
)


def build_payload() -> dict:
    charge = build_charge()
    volume = build_volume()
    rsigma = build_rsigma_to_curvature()
    charge_ready = charge["gate_passed"]
    volume_ready = volume["gate_passed"]
    return {
        "status": "janus-z2-global-state-prerequisite-derivability-audit-gate",
        "projected_baryon_noether_charge": {
            "can_derive_now": charge_ready,
            "primary_blocker": charge["primary_blocker"],
            "ready": charge_ready,
            "next_required": charge["next_required"],
        },
        "active_R_curv_volume": {
            "can_derive_now": volume_ready,
            "primary_blocker": volume["primary_blocker"],
            "ready": volume_ready,
            "nearest_RSigma_bridge_blocker": rsigma["primary_blocker"],
            "next_required": volume["next_required"],
        },
        "global_matter_state_can_be_derived_now": charge_ready and volume_ready,
        "non_rustine_blockers": [
            "derive active plus/minus spinor bundle and Z2Sigma charge projection",
            "derive active R_Sigma_solution_certificate or dimensional R_curv",
        ],
        "gate_passed": charge_ready and volume_ready,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Global State Prerequisite Derivability Audit Gate",
        "",
        (
            "Global matter state can be derived now: "
            f"`{payload['global_matter_state_can_be_derived_now']}`"
        ),
        "",
        "## Projected Baryon Noether Charge",
        f"- can derive now: `{payload['projected_baryon_noether_charge']['can_derive_now']}`",
        f"- blocker: `{payload['projected_baryon_noether_charge']['primary_blocker']}`",
        "",
        "## Active R_curv / Volume",
        f"- can derive now: `{payload['active_R_curv_volume']['can_derive_now']}`",
        f"- blocker: `{payload['active_R_curv_volume']['primary_blocker']}`",
        (
            "- nearest R_Sigma bridge blocker: "
            f"`{payload['active_R_curv_volume']['nearest_RSigma_bridge_blocker']}`"
        ),
        "",
        "## Non-Rustine Blockers",
    ]
    lines.extend(f"- `{item}`" for item in payload["non_rustine_blockers"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
