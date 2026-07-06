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
    build_payload as build_pullback_ratio,
)
from scripts.derive_p0_eft_janus_z2_sigma_reciprocal_projective_collar_probe import (
    build_payload as build_reciprocal_probe,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_reciprocal_collar_from_determinant_bridge.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_reciprocal_collar_from_determinant_bridge.json")


def build_payload() -> dict:
    audit = build_determinant_audit()
    pullback = build_pullback_ratio()
    probe = build_reciprocal_probe()
    formal_bridge_reciprocal_identity_declared = bool(
        audit["closure"]["B_plus_B_minus_reciprocal"]
    )
    active_pullback_reciprocal_identity_derived = bool(
        pullback["closure"]["reciprocal_identity_derived"]
    )
    active_lambda_law_derived = bool(
        pullback["closure"]["pullback_volume_ratio_derived"]
        and pullback["closure"]["plus_minus_metric_determinants_available"]
    )
    return {
        "status": "janus-z2-sigma-reciprocal-collar-from-determinant-bridge",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_reduction",
        "extension_allowed": False,
        "spatial_dimension": 3,
        "known_bridge_identity": "B_plus * B_minus = 1",
        "isotropic_endpoint_relation": "B_plus = (R_minus/R_plus)^3",
        "reciprocal_collar_needed": {
            "radius_law": "R_minus/ell_collar = ell_collar/R_plus",
            "lambda_law": "lambda_minus = 1/lambda_plus",
            "determinant_law": "B_plus(lambda) = lambda^-6",
            "fixed_point": "lambda = 1",
        },
        "formal_bridge_reciprocal_identity_declared": formal_bridge_reciprocal_identity_declared,
        "active_pullback_reciprocal_identity_derived": active_pullback_reciprocal_identity_derived,
        "active_lambda_law_derived": active_lambda_law_derived,
        "reciprocal_probe_selects_ratio": probe["R_Sigma_over_ell_collar_selected"],
        "candidate_ratio": probe["candidate_ratio"],
        "promotion_ready": False,
        "primary_blocker": "derive_B_plus_lambda_equals_lambda_minus_six_from_active_embedding",
        "interpretation": (
            "The formal determinant bridge declares B_plus/B_minus as reciprocal "
            "inverse volume factors. The active pullback derivation is still blocked "
            "on the embedding, and it does not yet derive the lambda dependence needed "
            "for a reciprocal collar. The exact missing theorem is B_plus(lambda)=lambda^-6, "
            "equivalently R_minus=ell_collar^2/R_plus."
        ),
        "next_required": [
            "derive_plus_minus_endpoint_metric_determinants_from_active_embedding",
            "prove_B_plus_lambda_equals_lambda_minus_six",
            "then_promote_reciprocal_probe_lambda_1_to_R_Sigma_solution_certificate",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Reciprocal Collar From Determinant Bridge",
        "",
        f"Formal bridge reciprocal identity declared: `{payload['formal_bridge_reciprocal_identity_declared']}`",
        f"Active pullback reciprocal identity derived: `{payload['active_pullback_reciprocal_identity_derived']}`",
        f"Active lambda law derived: `{payload['active_lambda_law_derived']}`",
        f"Candidate ratio: `{payload['candidate_ratio']}`",
        f"Promotion ready: `{payload['promotion_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Required Law",
    ]
    for key, value in payload["reciprocal_collar_needed"].items():
        lines.append(f"- `{key}`: `{value}`")
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
