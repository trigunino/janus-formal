from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_existing_action_core_ratio_audit_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_existing_action_core_ratio_audit_gate.json"
)


def build_payload() -> dict:
    candidate_terms = {
        "GHY_jump_terms": True,
        "israel_junction_conditions": True,
        "membrane_tension_B": True,
        "hassan_rosen_boundary_mass": True,
        "surface_intrinsic_EH_C_Rh_on_Sigma": False,
        "sqrt_intrinsic_counterterm_A_sqrt_Rh_on_Sigma": False,
    }
    can_supply_b = candidate_terms["membrane_tension_B"]
    can_supply_c = candidate_terms["surface_intrinsic_EH_C_Rh_on_Sigma"]
    return {
        "status": "janus-z2-sigma-existing-action-core-ratio-audit-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_audit",
        "checked_formal_modules": [
            "JanusFormal.P0ActionTermCoefficientDerivation",
            "JanusFormal.P0CandidateOrbifoldActionInstantiation",
            "JanusFormal.P0EFTJanusSigmaBoundaryActionSupportGate",
        ],
        "candidate_terms": candidate_terms,
        "core_radius_stationarity": {
            "needed_density": "A sqrt(R[h]) + B + C R[h]",
            "needed_ratio": "C/B",
            "existing_action_supplies_B": can_supply_b,
            "existing_action_supplies_C": can_supply_c,
            "existing_action_derives_C_over_B": can_supply_b and can_supply_c,
        },
        "decision": (
            "existing_action_does_not_fix_RSigma"
            if not (can_supply_b and can_supply_c)
            else "existing_action_can_fix_RSigma"
        ),
        "gate_passed": True,
        "primary_blocker": "missing_surface_intrinsic_EH_coefficient_C"
        if not can_supply_c
        else "none",
        "next_required": [
            "derive or reject a Sigma-localized intrinsic curvature term C R[h]",
            "if rejected, treat R_Sigma as open modulus or find another radius-fixing principle",
            "if accepted, derive C/B from the same action, not by fit",
        ]
        if not (can_supply_b and can_supply_c)
        else [],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Existing Action Core Ratio Audit Gate",
        "",
        f"Decision: `{payload['decision']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Core Ratio",
        f"- Existing action supplies `B`: `{payload['core_radius_stationarity']['existing_action_supplies_B']}`",
        f"- Existing action supplies `C`: `{payload['core_radius_stationarity']['existing_action_supplies_C']}`",
    ]
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
