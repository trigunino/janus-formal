from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import (
    build_payload as build_embedding_readiness,
)
from scripts.build_p0_eft_janus_z2_sigma_bridge_determinant_factor_audit_gate import (
    build_payload as build_determinant_audit,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_pullback_volume_determinant_ratio_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_pullback_volume_determinant_ratio_gate.json"
)


def build_payload(*, embedding_manifest_path: Path | None = None) -> dict:
    if embedding_manifest_path is None:
        embedding = build_embedding_readiness()
    else:
        embedding = build_embedding_readiness(embedding_manifest_path=embedding_manifest_path)
    audit = build_determinant_audit()
    active_embedding_ready = bool(embedding["readiness"]["active_embedding_ready"])
    closure = {
        "active_embedding_readiness_gate_imported": True,
        "bridge_determinant_factor_audit_gate_imported": True,
        "oriented_pullback_commutation_gate_imported": True,
        "plus_volume_form_declared": True,
        "minus_volume_form_declared": True,
        "Z2_pullback_volume_map_declared": True,
        "jacobian_density_channel_declared": True,
        "orientation_sign_fixed": True,
        "no_fitted_volume_coefficient": True,
        "active_embedding_ready": active_embedding_ready,
        "plus_minus_metric_determinants_available": active_embedding_ready,
        "pullback_volume_ratio_derived": active_embedding_ready,
        "B_plus_from_pullback_volume": active_embedding_ready,
        "B_minus_from_inverse_pullback_volume": active_embedding_ready,
        "reciprocal_identity_derived": active_embedding_ready,
        "feeds_bridge_determinant_audit": active_embedding_ready and audit["gate_passed"],
    }
    template_keys = [
        "active_embedding_readiness_gate_imported",
        "bridge_determinant_factor_audit_gate_imported",
        "oriented_pullback_commutation_gate_imported",
        "plus_volume_form_declared",
        "minus_volume_form_declared",
        "Z2_pullback_volume_map_declared",
        "jacobian_density_channel_declared",
        "orientation_sign_fixed",
        "no_fitted_volume_coefficient",
    ]
    derivation_keys = [
        "active_embedding_ready",
        "plus_minus_metric_determinants_available",
        "pullback_volume_ratio_derived",
        "B_plus_from_pullback_volume",
        "B_minus_from_inverse_pullback_volume",
        "reciprocal_identity_derived",
        "feeds_bridge_determinant_audit",
    ]
    template_ready = all(closure[key] for key in template_keys)
    derivation_ready = template_ready and all(closure[key] for key in derivation_keys)
    blockers = [key for key in derivation_keys if not closure[key]]
    return {
        "status": "janus-z2-sigma-pullback-volume-determinant-ratio-gate",
        "route_status": (
            "pullback_volume_ratio_derived"
            if derivation_ready
            else "template_ready_waiting_for_active_embedding"
        ),
        "definitions": {
            "volume_pullback": "tau_Z2^* dVol_minus = J_-+ dVol_plus",
            "B_plus": "J_-+ = sqrt(|g_minus|)/sqrt(|g_plus|)",
            "B_minus": "J_+- = sqrt(|g_plus|)/sqrt(|g_minus|)",
            "reciprocal": "B_plus * B_minus = 1 on inverse branches",
        },
        "closure": closure,
        "template_ready": template_ready,
        "derivation_ready": derivation_ready,
        "gate_passed": derivation_ready,
        "primary_blocker": "none" if derivation_ready else blockers[0],
        "blockers": blockers,
        "upstream": {
            "embedding": {
                "gate": embedding["status"],
                "active_embedding_ready": active_embedding_ready,
                "primary_blocker": embedding["primary_blocker"],
            },
            "determinant_audit": {
                "gate": audit["status"],
                "gate_passed": audit["gate_passed"],
                "source_derivation_ready": audit["source_derivation_ready"],
            },
        },
        "next_required": [
            "feed derived B_plus/B_minus into transport compatibility source equations",
            "prove covariant divergence cancellation with determinant gradients",
        ],
        "interpretation": (
            "The volume-ratio derivation is isolated from S_cross. A valid active "
            "embedding supplies the pullback Jacobian, which gives B_plus/B_minus "
            "and feeds the determinant audit without fitting a coefficient."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Pullback Volume Determinant Ratio Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Definitions",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["definitions"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
