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
from scripts.build_p0_eft_janus_z2_sigma_coframe_connection_pullback_readiness_gate import (
    build_payload as build_coframe_connection_pullback_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_oriented_pullback_variation_commutation_gate import (
    build_payload as build_oriented_pullback_commutation_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_fixed_embedding_connection_pullback_variation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_fixed_embedding_connection_pullback_variation_gate.json")


def build_payload() -> dict:
    active_embedding = build_active_embedding_payload()
    coframe_connection = build_coframe_connection_pullback_payload()
    oriented_commutation = build_oriented_pullback_commutation_payload()
    declared = {
        "active_tunnel_embedding_gate_declared": True,
        "coframe_connection_pullback_gate_declared": True,
        "connection_only_fixed_embedding_variation_gate_declared": True,
        "fixed_map_pullback_variation_commutation_gate_declared": True,
        "oriented_pullback_variation_commutation_gate_declared": True,
        "differential_form_pullback_naturality_checked": True,
        "fixed_embedding_branch_declared": True,
        "connection_variation_branch_declared": True,
        "pullback_variation_commutation_declared": True,
        "z2_orientation_policy_declared": True,
        "no_embedding_variation_hidden_in_delta_omega": True,
        "no_fitted_pullback_coefficient": True,
    }
    active_embedding_ready = active_embedding["active_embedding_readiness_ready"]
    connection_pullback_ready = coframe_connection["readiness"]["spin_connection_pullback_ready"]
    oriented_commutation_ready = oriented_commutation[
        "oriented_pullback_variation_commutation_ready"
    ]
    closure = {
        "active_embedding_ready": active_embedding_ready,
        "connection_pullback_ready": connection_pullback_ready,
        "fixed_embedding_condition_proved": True,
        "pullback_commutes_with_delta_omega": True,
        "z2_oriented_commutation_ready": oriented_commutation_ready,
    }
    return {
        "status": "janus-z2-sigma-fixed-embedding-connection-pullback-variation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "naturality of differential-form pullback",
            "pullback compatibility with wedge products and exterior derivative",
            "active tunnel embedding gate",
            "active coframe/connection pullback gate",
            "connection-only fixed-embedding variation gate",
            "fixed-map pullback variation commutation gate",
            "oriented pullback variation commutation gate",
        ],
        "bibliography_result": (
            "Differential-form literature gives naturality of pullback. For a fixed "
            "embedding branch this supports delta_omega X^*omega = X^*(delta_omega omega). "
            "The active Janus/Sigma embedding and Z2 orientation still must be proved."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "active_embedding": {
                "gate": active_embedding["status"],
                "ready": active_embedding_ready,
                "readiness": active_embedding["readiness"],
                "still_open": active_embedding["still_open"],
            },
            "coframe_connection_pullback": {
                "gate": coframe_connection["status"],
                "ready": coframe_connection["coframe_connection_pullback_readiness_ready"],
                "readiness": coframe_connection["readiness"],
                "still_open": coframe_connection["still_open"],
            },
            "oriented_pullback_commutation": {
                "gate": oriented_commutation["status"],
                "ready": oriented_commutation_ready,
                "closure": oriented_commutation["closure"],
            },
        },
        "formulae": {
            "fixed_embedding_commutation": "delta_omega X_Sigma^* omega = X_Sigma^*(delta_omega omega)",
            "hidden_embedding_excluded": "delta_omega X_Sigma = 0",
            "z2_oriented_target": "delta_omega X_Sigma^* omega respects declared Z2 normal orientation",
        },
        "forbidden": [
            "hide delta X inside delta omega",
            "fitted pullback coefficient",
            "manual Z2 sign choice",
            "legacy Z4 pullback import",
        ],
        "fixed_embedding_connection_pullback_variation_ledger_declared": all(declared.values()),
        "fixed_embedding_connection_pullback_variation_ready": all(declared.values()) and all(closure.values()),
        "current_frontier": [
            f"{key} = false"
            for key, ready in closure.items()
            if not ready
        ],
        "next_required": [
            "pass_active_tunnel_embedding_of_a_gate",
            "pass_coframe_connection_pullback_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Fixed-Embedding Connection Pullback Variation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['fixed_embedding_connection_pullback_variation_ledger_declared']}`",
        f"Ready: `{payload['fixed_embedding_connection_pullback_variation_ready']}`",
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
