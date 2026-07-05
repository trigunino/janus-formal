from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_boundary_spinor_restriction_gate import (
    build_payload as build_boundary_spinor_restriction_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spinor_boundary_projection_map_gate import (
    build_payload as build_spinor_boundary_projection_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_tangent_normal_orientation_gate import (
    build_payload as build_tangent_normal_orientation_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_spinor_projection_attack_order_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_spinor_projection_attack_order_gate.json")


def build_payload() -> dict:
    boundary = build_boundary_spinor_restriction_payload()
    normal = build_tangent_normal_orientation_payload()
    projection = build_spinor_boundary_projection_payload()
    closure = {
        "boundary_spinor_restriction_ready": boundary["boundary_spinor_restriction_ready"],
        "tangent_normal_orientation_ready": normal["tangent_normal_orientation_ready"],
        "unit_normal_clifford_action_ready": projection["closure"]["unit_normal_Clifford_action_ready"],
        "projection_idempotent_ready": projection["closure"]["projection_idempotent_ready"],
        "projection_self_adjoint_ready": projection["closure"]["projection_self_adjoint_ready"],
        "spinor_boundary_projection_map_ready": projection["spinor_boundary_projection_map_ready"],
    }
    primary_blocker = (
        normal.get("primary_blocker", "active_embedding_and_unit_normals")
        if not normal["tangent_normal_orientation_ready"]
        else "boundary_spinor_restriction"
        if not boundary["boundary_spinor_restriction_ready"]
        else "unit_normal_clifford_projection_algebra"
    )
    return {
        "status": "janus-z2-sigma-spinor-projection-attack-order-gate",
        "active_core": "Z2_tunnel_Sigma",
        "closure": closure,
        "primary_blocker": primary_blocker,
        "attack_order_ready": all(closure.values()),
        "no_free_boundary_phase": True,
        "no_observational_spinor_fit": True,
        "no_archived_z4_projection": True,
        "upstream_frontiers": {
            "boundary_spinor_restriction": {
                "gate": boundary["status"],
                "ready": boundary["boundary_spinor_restriction_ready"],
                "closure": boundary["closure"],
            },
            "tangent_normal_orientation": {
                "gate": normal["status"],
                "ready": normal["tangent_normal_orientation_ready"],
                "closure": normal["closure"],
                "primary_blocker": normal.get("primary_blocker"),
            },
            "spinor_boundary_projection": {
                "gate": projection["status"],
                "ready": projection["spinor_boundary_projection_map_ready"],
                "closure": projection["closure"],
            },
        },
        "next_required": [
            "close_active_embedding_and_unit_normals",
            "close_boundary_spinor_restriction",
            "derive_unit_normal_clifford_action",
            "prove_projection_idempotent_and_self_adjoint",
            "then_close_reflecting_spinor_boundary_current",
        ],
        "gate_passed": all(closure.values()),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Spinor Projection Attack Order Gate",
                "",
                f"Primary blocker: `{payload['primary_blocker']}`",
                f"Gate passed: `{payload['gate_passed']}`",
                "",
                "## Next Required",
                *[f"- `{item}`" for item in payload["next_required"]],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
