from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_integrability_gate import (
    build_payload as build_integrability_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_primitive_integration_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_primitive_integration_gate.json")


def build_payload(*, integrability_payload: dict | None = None, primitive_payload: dict | None = None) -> dict:
    integrability = integrability_payload or build_integrability_payload()
    primitive = primitive_payload or {}
    declared = {
        "counterterm_condition_declared": True,
        "exact_residual_one_form_required": True,
        "local_primitive_integration_declared": True,
        "uniqueness_transport_declared": True,
        "observational_fit_forbidden": True,
    }
    residual_exact = bool(integrability["closure"]["residual_one_form_exact"])
    closure = {
        "residual_one_form_exact": residual_exact,
        "primitive_density_supplied": bool(primitive.get("primitive_density_supplied", False)),
        "primitive_cancels_residual": bool(primitive.get("primitive_cancels_residual", False)),
        "primitive_unique_up_to_constant": bool(primitive.get("primitive_unique_up_to_constant", False)),
        "no_new_counterterm_freedom": bool(primitive.get("no_new_counterterm_freedom", False)),
    }
    ready = all(declared.values()) and all(closure.values())
    if not residual_exact:
        primary_blocker = integrability.get("primary_blocker", "counterterm_residual_exactness")
    elif not closure["primitive_density_supplied"]:
        primary_blocker = "counterterm_primitive_density"
    elif not closure["primitive_cancels_residual"]:
        primary_blocker = "counterterm_primitive_residual_cancellation"
    elif not closure["primitive_unique_up_to_constant"]:
        primary_blocker = "counterterm_primitive_uniqueness"
    elif not closure["no_new_counterterm_freedom"]:
        primary_blocker = "counterterm_no_new_freedom"
    else:
        primary_blocker = "none"
    return {
        "status": "janus-z2-sigma-counterterm-primitive-integration-gate",
        "active_core": "Z2_tunnel_Sigma",
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "residual_integrability": {
                "gate": integrability["status"],
                "ready": integrability["counterterm_residual_integrability_ready"],
                "primary_blocker": integrability.get("primary_blocker", "counterterm_residual_integrability"),
                "closure": integrability["closure"],
            },
        },
        "structural_formulae": {
            "counterterm_condition": "delta S_ct = - alpha_res",
            "primitive_condition": "alpha_res exact => S_ct = - integral alpha_res",
        },
        "counterterm_primitive_integration_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "current_frontier": [
            f"{key} = false"
            for key, value in closure.items()
            if not value
        ],
        "next_required": []
        if ready
        else [
            "pass_counterterm_residual_integrability_gate",
            "integrate_exact_residual_one_form_to_local_primitive",
            "prove_primitive_cancels_residual",
            "prove_no_new_counterterm_freedom",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Primitive Integration Gate",
        "",
        f"Ready: `{payload['counterterm_primitive_integration_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Current Frontier",
    ]
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
