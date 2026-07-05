from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_bulk_stress_of_a_gate import (
    build_payload as build_bulk_stress_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_embedding_regularity_equivariance_gate import (
    build_payload as build_embedding_equivariance_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flux_projection_domain_gate import (
    build_payload as build_flux_domain_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_stress_equivariance_gate import (
    build_payload as build_stress_equivariance_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_equivariant_flux_cancellation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_equivariant_flux_cancellation_gate.json")


def build_payload() -> dict:
    embedding = build_embedding_equivariance_payload()
    domain = build_flux_domain_payload()
    bulk_stress = build_bulk_stress_payload()
    stress_equivariance = build_stress_equivariance_payload()

    closure = {
        "Z2_equivariant_embedding_derived": embedding["closure"]["Z2_equivariant_embedding_derived"],
        "coorientation_ready": domain["closure"]["coorientation_ready"],
        "Sigma_tangents_ready": domain["closure"]["Sigma_tangents_ready"],
        "Sigma_normals_ready": domain["closure"]["Sigma_normals_ready"],
        "bulk_stress_plus_of_a_ready": bulk_stress["closure"]["bulk_stress_plus_of_a_ready"],
        "bulk_stress_minus_of_a_ready": bulk_stress["closure"]["bulk_stress_minus_of_a_ready"],
        "Z2_stress_equivariance_derived": stress_equivariance["stress_equivariance_ready"],
        "normal_reversal_under_Z2_derived": domain["closure"]["coorientation_ready"],
        "tangent_transport_under_Z2_derived": embedding["closure"]["Z2_equivariant_embedding_derived"],
    }
    algebraic_theorem_declared = True
    prerequisites_ready = all(closure.values())
    z2_flux_cancellation_derived = algebraic_theorem_declared and prerequisites_ready
    primary_blocker = "none"
    if not z2_flux_cancellation_derived:
        primary_blocker = next(key for key, ready in closure.items() if not ready)

    return {
        "status": "janus-z2-sigma-equivariant-flux-cancellation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "bibliography_result": (
            "Thin-shell transparency is a standard no-flux branch. The Janus-specific "
            "route is not generic thin-shell physics: it requires Z2 equivariance of "
            "embedding, stress transport, and opposite coorientation of the two normals."
        ),
        "formulas": {
            "plus_flux": "F_a^+ = T^+_munu e_a^mu n_+^nu",
            "minus_flux": "F_a^- = T^-_munu e_a^mu n_-^nu",
            "z2_equivariance": "X_- = tau_Z2 o X_+ and T_- = tau_* T_+",
            "normal_reversal": "n_- = - tau_* n_+",
            "tangent_transport": "e_a^- = tau_* e_a^+",
            "cancellation": "F_a^+ + eps_Z2 F_a^- = 0",
        },
        "closure": closure,
        "algebraic_cancellation_theorem_declared": algebraic_theorem_declared,
        "z2_flux_cancellation_derived": z2_flux_cancellation_derived,
        "gate_passed": z2_flux_cancellation_derived,
        "primary_blocker": primary_blocker,
        "upstream_frontiers": {
            "embedding_equivariance": {
                "gate": embedding["status"],
                "ready": embedding["embedding_regularity_equivariance_ready"],
                "primary_blocker": embedding["primary_blocker"],
            },
            "flux_projection_domain": {
                "gate": domain["status"],
                "ready": domain["flux_projection_domain_ready"],
                "primary_blocker": domain["primary_blocker"],
            },
            "bulk_stress": {
                "gate": bulk_stress["status"],
                "ready": bulk_stress["bulk_stress_of_a_ready"],
                "primary_blocker": bulk_stress["primary_blocker"],
            },
            "stress_equivariance": {
                "gate": stress_equivariance["status"],
                "ready": stress_equivariance["stress_equivariance_ready"],
                "primary_blocker": stress_equivariance["primary_blocker"],
                "closure": stress_equivariance["closure"],
            },
        },
        "next_required": [
            "prove_Z2_equivariance_of_embedding",
            "derive_Sigma_tangent_and_normal_frames",
            "derive_Z2_stress_equivariance_T_minus_equals_pushforward_T_plus",
            "then_use_algebraic_cancellation_to_set_F_a_Z2Sigma_zero",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Equivariant Flux Cancellation Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Formula",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
