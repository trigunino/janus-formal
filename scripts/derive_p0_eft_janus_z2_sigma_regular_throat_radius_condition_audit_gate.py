from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_regular_throat_radius_condition_audit_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_regular_throat_radius_condition_audit_gate.json"
)


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-regular-throat-radius-condition-audit-gate",
        "active_core": "Z2_tunnel_Sigma",
        "route": "smooth resolved Z2 tunnel throat regularity",
        "regularity_conditions": {
            "Z2_even_induced_metric": True,
            "Z2_odd_normal_derivative": True,
            "no_conical_defect_requires_smooth_collar_angle": True,
            "minimal_throat_condition_declared": True,
        },
        "derivable": {
            "parity_of_h_ab_under_normal_reflection": True,
            "parity_of_K_ab_under_normal_reflection": True,
            "jump_or_mean_curvature_constraints": True,
            "absolute_R_Sigma_value": False,
            "R_Sigma_of_a": False,
        },
        "reason": (
            "Smoothness and Z2 regularity constrain derivatives, parity and junction "
            "data at the throat. They do not choose the absolute radius unless the "
            "ambient curvature scale, collar thickness, or a surface potential is "
            "already fixed."
        ),
        "gate_passed": True,
        "R_Sigma_solution_certificate_ready": False,
        "primary_blocker": "regularity_constraints_are_scale_invariant",
        "next_required": [
            "combine regularity with a scale-fixing action term",
            "or derive ambient curvature scale from existing Janus equations",
            "or keep the throat radius as a modulus",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Regular Throat Radius Condition Audit Gate",
        "",
        f"Primary blocker: `{payload['primary_blocker']}`",
        f"R_Sigma solution ready: `{payload['R_Sigma_solution_certificate_ready']}`",
        "",
        payload["reason"],
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
