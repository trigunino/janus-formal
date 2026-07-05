from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_extrinsic_curvature_variation_transport_gate import (
    build_payload as build_extrinsic_curvature_variation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_metric_variation_transport_gate import (
    build_payload as build_metric_variation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_torsion_pullback_variation_transport_gate import (
    build_payload as build_torsion_pullback_variation_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_variation_transport_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_variation_transport_readiness_gate.json")


def build_payload() -> dict:
    metric = build_metric_variation_payload()
    extrinsic = build_extrinsic_curvature_variation_payload()
    torsion = build_torsion_pullback_variation_payload()
    declared = {
        "tetrad_variation_transport_gate_imported": True,
        "metric_variation_transport_gate_imported": True,
        "extrinsic_curvature_variation_transport_gate_imported": True,
        "torsion_pullback_variation_transport_gate_imported": True,
        "no_metric_only_shortcut": True,
        "no_fitted_tetrad_residual_coefficient": True,
    }
    readiness = {
        "induced_metric_variation_transport_ready": metric["tetrad_metric_variation_transport_ready"],
        "extrinsic_curvature_variation_transport_ready": extrinsic["deltaK_transport_ready"],
        "torsion_pullback_variation_transport_ready": torsion[
            "tetrad_torsion_pullback_variation_ready"
        ],
    }
    readiness["tetrad_variation_transport_ready"] = all(readiness.values())
    return {
        "status": "janus-z2-sigma-counterterm-tetrad-variation-transport-readiness-gate",
        "active_core": "Z2_tunnel_Sigma",
        "declared": declared,
        "readiness": readiness,
        "subgate_status": {
            "delta_e_to_delta_h": "closed_by_tetrad_metric_variation_transport_gate",
            "delta_e_to_delta_K": "open_on_active_embedding_frame_connection_variation",
            "delta_e_to_torsion_pullback": "open_on_sigma_pullback_orientation_allowed_basis",
        },
        "nearest_missing_subgate": {
            "name": "delta_e_to_delta_K",
            "gate": "counterterm_tetrad_extrinsic_curvature_variation_transport_gate",
            "reason": (
                "metric variation transport is closed; the next tetrad transport "
                "needed by the residual channel is extrinsic-curvature variation"
            ),
            "next_required": "close_tetrad_extrinsic_curvature_variation_transport_gate",
        },
        "upstream_frontiers": {
            "metric_variation": {
                "gate": metric["status"],
                "ready": metric["tetrad_metric_variation_transport_ready"],
                "closure": metric["closure"],
            },
            "extrinsic_curvature_variation": {
                "gate": extrinsic["status"],
                "ready": extrinsic["deltaK_transport_ready"],
                "closure": extrinsic["closure"],
                "current_frontier": extrinsic["current_frontier"],
            },
            "torsion_pullback_variation": {
                "gate": torsion["status"],
                "ready": torsion["tetrad_torsion_pullback_variation_ready"],
                "closure": torsion["closure"],
                "still_open": torsion["still_open"],
            },
        },
        "tetrad_variation_readiness_ledger_declared": all(declared.values()),
        "tetrad_variation_readiness_ready": all(declared.values()) and all(readiness.values()),
        "current_frontier": [
            f"{key} = false"
            for key, ready in readiness.items()
            if not ready
        ],
        "next_required": [
            "close_tetrad_extrinsic_curvature_variation_transport_gate",
            "close_tetrad_torsion_pullback_variation_transport_gate",
            "then_feed_tetrad_variation_transport_ready_to_tetrad_residual_channel_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Tetrad Variation Transport Readiness Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['tetrad_variation_readiness_ledger_declared']}`",
        f"Readiness ready: `{payload['tetrad_variation_readiness_ready']}`",
        "",
        "## Subgate Status",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["subgate_status"].items())
    lines.extend(
        [
            "",
            "## Nearest Missing Subgate",
            f"`{payload['nearest_missing_subgate']['name']}`",
        ]
    )
    lines.extend(["", "## Current Frontier"])
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
