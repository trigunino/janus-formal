from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_bridge_determinant_factor_audit_gate import (
    build_payload as build_determinant_audit,
)
from scripts.build_p0_eft_janus_z2_sigma_pullback_volume_determinant_ratio_gate import (
    build_payload as build_pullback_volume,
)
from scripts.build_p0_eft_janus_z2_sigma_transport_compatibility_source_equation_gate import (
    build_payload as build_transport_source,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_determinant_gradient_divergence_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_determinant_gradient_divergence_gate.json"
)


def build_payload(*, embedding_manifest_path: Path | None = None) -> dict:
    audit = build_determinant_audit()
    if embedding_manifest_path is None:
        pullback = build_pullback_volume()
        transport_source = build_transport_source()
    else:
        pullback = build_pullback_volume(embedding_manifest_path=embedding_manifest_path)
        transport_source = build_transport_source(embedding_manifest_path=embedding_manifest_path)
    b_ready = bool(
        pullback["closure"]["B_plus_from_pullback_volume"]
        and pullback["closure"]["B_minus_from_inverse_pullback_volume"]
    )
    closure = {
        "bridge_determinant_audit_gate_imported": True,
        "pullback_volume_ratio_gate_imported": True,
        "transport_compatibility_source_equation_gate_imported": True,
        "B_plus_covariant_gradient_declared": True,
        "B_minus_covariant_gradient_declared": True,
        "plus_product_rule_declared": True,
        "minus_product_rule_declared": True,
        "gradients_kept_outside_K": True,
        "gradients_kept_outside_Qcross": True,
        "no_determinant_gradient_absorption": bool(
            audit["closure"]["no_Qcross_determinant_absorption"]
        ),
        "B_plus_from_pullback_volume_ready": bool(
            pullback["closure"]["B_plus_from_pullback_volume"]
        ),
        "B_minus_from_pullback_volume_ready": bool(
            pullback["closure"]["B_minus_from_inverse_pullback_volume"]
        ),
        "plus_divergence_split_derived": b_ready,
        "minus_divergence_split_derived": b_ready,
        "feeds_plus_compatibility_equation": b_ready,
        "feeds_minus_compatibility_equation": b_ready,
    }
    template_keys = [
        "bridge_determinant_audit_gate_imported",
        "pullback_volume_ratio_gate_imported",
        "transport_compatibility_source_equation_gate_imported",
        "B_plus_covariant_gradient_declared",
        "B_minus_covariant_gradient_declared",
        "plus_product_rule_declared",
        "minus_product_rule_declared",
        "gradients_kept_outside_K",
        "gradients_kept_outside_Qcross",
        "no_determinant_gradient_absorption",
    ]
    ready_keys = [
        "B_plus_from_pullback_volume_ready",
        "B_minus_from_pullback_volume_ready",
        "plus_divergence_split_derived",
        "minus_divergence_split_derived",
        "feeds_plus_compatibility_equation",
        "feeds_minus_compatibility_equation",
    ]
    template_ready = all(closure[key] for key in template_keys)
    divergence_ready = template_ready and all(closure[key] for key in ready_keys)
    blockers = [key for key in ready_keys if not closure[key]]
    return {
        "status": "janus-z2-sigma-determinant-gradient-divergence-gate",
        "route_status": (
            "determinant_gradient_divergence_split_ready"
            if divergence_ready
            else "template_ready_waiting_for_pullback_volume_b_factors"
        ),
        "identities": {
            "plus_cross_divergence": (
                "D_plus_nu(B_plus K_plus^{mu nu}) = "
                "(D_plus_nu B_plus) K_plus^{mu nu} + B_plus D_plus_nu K_plus^{mu nu}"
            ),
            "minus_cross_divergence": (
                "D_minus_nu(B_minus K_minus^{mu nu}) = "
                "(D_minus_nu B_minus) K_minus^{mu nu} + B_minus D_minus_nu K_minus^{mu nu}"
            ),
        },
        "closure": closure,
        "template_ready": template_ready,
        "divergence_split_ready": divergence_ready,
        "gate_passed": divergence_ready,
        "primary_blocker": "none" if divergence_ready else blockers[0],
        "blockers": blockers,
        "upstream": {
            "pullback_volume": {
                "gate": pullback["status"],
                "derivation_ready": pullback["derivation_ready"],
                "primary_blocker": pullback["primary_blocker"],
            },
            "transport_source_equation": {
                "gate": transport_source["status"],
                "source_derivation_ready": transport_source["source_derivation_ready"],
                "primary_blocker": transport_source["primary_blocker"],
            },
        },
        "next_required": [
            "match determinant-gradient terms with transported connection-force residuals",
            "then prove plus/minus transport compatibility source equations",
        ],
        "interpretation": (
            "The determinant-gradient terms are isolated by the covariant product rule. "
            "They remain outside K and Q_cross, so later compatibility proofs must cancel "
            "them explicitly rather than hide them in the transport map."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Determinant Gradient Divergence Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Identities",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["identities"].items())
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
