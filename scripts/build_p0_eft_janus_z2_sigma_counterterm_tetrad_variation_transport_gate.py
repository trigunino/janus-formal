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

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_variation_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_variation_transport_gate.json")


def build_payload() -> dict:
    metric = build_metric_variation_payload()
    extrinsic = build_extrinsic_curvature_variation_payload()
    torsion = build_torsion_pullback_variation_payload()
    declared = {
        "tetrad_residual_channel_imported": True,
        "extrinsic_curvature_gate_imported": True,
        "torsion_pullback_gate_imported": True,
        "palatini_holst_tetrad_variation_bibliography_checked": True,
        "coframe_variation_basis_declared": True,
        "delta_e_to_delta_h_declared": True,
        "delta_e_to_delta_K_declared": True,
        "delta_e_to_delta_torsion_pullback_declared": True,
        "z2_orientation_variation_policy_declared": True,
        "no_metric_only_shortcut": True,
        "no_fitted_tetrad_residual_coefficient": True,
    }
    closure = {
        "induced_metric_variation_transport_ready": metric[
            "tetrad_metric_variation_transport_ready"
        ],
        "extrinsic_curvature_variation_transport_ready": extrinsic[
            "deltaK_transport_ready"
        ],
        "torsion_pullback_variation_transport_ready": torsion[
            "tetrad_torsion_pullback_variation_ready"
        ],
    }
    closure["tetrad_variation_transport_ready"] = all(closure.values())
    return {
        "status": "janus-z2-sigma-counterterm-tetrad-variation-transport-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Palatini-Holst coframe/tetrad variation",
            "hypersurface induced metric and extrinsic curvature variation",
            "Cartan torsion pullback variation on Sigma",
        ],
        "source_links": [
            "https://arxiv.org/abs/gr-qc/9209012",
            "https://link.springer.com/article/10.1007/BF02710419",
            "https://www.sciencedirect.com/topics/mathematics/second-fundamental-form",
        ],
        "bibliography_result": (
            "Standard first-order variation supplies the coframe channel, but active "
            "Janus/Sigma still needs transport of delta e into delta h, delta K and "
            "torsion-pullback variations before R_e can be explicit."
        ),
        "declared": declared,
        "closure": closure,
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
        "transport_targets": [
            "delta e -> delta h_ab",
            "delta e -> delta K_ab",
            "delta e -> delta X_Sigma^*T^I",
            "Z2 orientation variation policy",
        ],
        "tetrad_variation_transport_ledger_declared": all(declared.values()),
        "tetrad_variation_transport_ready": all(declared.values()) and all(closure.values()),
        "current_frontier": [
            f"{key} = false"
            for key, ready in closure.items()
            if not ready
        ],
        "next_required": [
            "derive_delta_e_to_delta_h_transport",
            "derive_delta_e_to_delta_K_transport_from_embedding_extrinsic_curvature_gate",
            "derive_delta_e_to_torsion_pullback_variation_transport",
            "feed_tetrad_variation_transport_to_tetrad_residual_channel_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Tetrad Variation Transport Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['tetrad_variation_transport_ledger_declared']}`",
        f"Transport ready: `{payload['tetrad_variation_transport_ready']}`",
        "",
        "## Transport Targets",
    ]
    lines.extend(f"- `{item}`" for item in payload["transport_targets"])
    lines.extend(["", "## Current Frontier"])
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
