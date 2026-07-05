from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import (
    build_payload as build_active_embedding_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_channel_frontier_gate import (
    build_payload as build_residual_channel_frontier_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_residual_channel_gate import (
    build_payload as build_tetrad_residual_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_throat_radius_solution_frontier_gate import (
    build_payload as build_throat_radius_frontier_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_attack_order_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_attack_order_gate.json")


def build_payload() -> dict:
    residual_frontier = build_residual_channel_frontier_payload()
    tetrad = build_tetrad_residual_payload()
    embedding = build_active_embedding_payload()
    throat = build_throat_radius_frontier_payload()

    nearest = residual_frontier["nearest_residual_channel_frontier"]
    active_embedding_ready = embedding["active_embedding_readiness_ready"]
    throat_radius_ready = throat["status_flags"]["R_Sigma_of_a_ready"]
    tetrad_ready = tetrad["counterterm_tetrad_residual_channel_ready"]

    declared = {
        "residual_channel_frontier_imported": True,
        "tetrad_residual_channel_imported": True,
        "active_embedding_readiness_imported": True,
        "throat_radius_solution_frontier_imported": True,
        "attack_order_is_diagnostic_only": True,
        "no_counterterm_channel_dropped": True,
        "no_fit_shortcut": True,
        "no_legacy_z4_import": True,
    }
    closure = {
        "nearest_channel_identified": nearest["channel"] == "tetrad",
        "tetrad_channel_is_nearest_not_ready": nearest["channel"] == "tetrad" and not tetrad_ready,
        "active_embedding_ready": active_embedding_ready,
        "R_Sigma_solution_certificate_ready": throat_radius_ready,
        "counterterm_attack_order_ready": False,
    }
    upstream_blocker = (
        "R_Sigma_solution_certificate"
        if not throat_radius_ready
        else "active_embedding_readiness"
        if not active_embedding_ready
        else "tetrad_residual_channel"
    )
    return {
        "status": "janus-z2-sigma-counterterm-attack-order-gate",
        "active_core": "Z2_tunnel_Sigma",
        "declared": declared,
        "closure": closure,
        "attack_order": [
            "close_R_Sigma_solution_certificate",
            "materialize_active_embedding_geometry",
            "close_tetrad_deltaK_and_torsion_pullback_transport",
            "compute_tetrad_residual_channel",
            "then_close_remaining_connection_spinor_embedding_matter_flux_channels",
            "then_form_exact_residual_one_form_and_counterterm_primitive",
        ],
        "upstream_frontiers": {
            "residual_channel_frontier": {
                "gate": residual_frontier["status"],
                "ready": residual_frontier["residual_channel_frontier_ready"],
                "nearest": nearest,
            },
            "tetrad_residual_channel": {
                "gate": tetrad["status"],
                "ready": tetrad_ready,
                "current_frontier": tetrad["current_frontier"],
            },
            "active_embedding": {
                "gate": embedding["status"],
                "ready": active_embedding_ready,
                "still_open": embedding["still_open"],
                "nearest": embedding["nearest_embedding_frontier"],
            },
            "throat_radius_solution": {
                "gate": throat["status"],
                "R_Sigma_of_a_ready": throat_radius_ready,
                "current_frontier": throat["current_frontier"],
                "nearest_radial_block_frontier": throat["nearest_radial_block_frontier"],
            },
        },
        "primary_blocker": upstream_blocker,
        "gate_passed": all(declared.values()) and all(closure.values()),
        "next_required": [
            "continue_R_Sigma_solution_frontier",
            "reduce_matter_flux_and_counterterm_radial_blocks",
            "emit_active_embedding_geometry_manifest",
            "rerun_counterterm_tetrad_residual_channel_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Attack Order Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Attack Order",
    ]
    lines.extend(f"- `{item}`" for item in payload["attack_order"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
