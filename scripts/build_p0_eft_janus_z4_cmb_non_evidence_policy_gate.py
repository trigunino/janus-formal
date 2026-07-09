from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_cmb_non_evidence_policy_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_cmb_non_evidence_policy_gate.json")


def build_payload() -> dict:
    policy = {
        "z4_cmb_attempts_kept_for_diagnostics": True,
        "cyclic_z4_not_used_by_active_geometry": True,
        "no_monodromy_proof_available": True,
        "no_new_z4_physics_allowed": True,
        "z4_modules_diagnostic_only": True,
        "active_core_is_z2_tunnel_sigma": True,
    }
    return {
        "status": "janus-z4-cmb-non-evidence-policy-gate",
        "policy": policy,
        "z4_cmb_marked_non_evidence": all(policy.values()),
        "active_core": "Z2_tunnel_Sigma",
        "next_allowed_model_work": [
            "RP4_Pin_sign_audit",
            "Sigma_boundary_action_support",
            "Z2_projective_tunnel_orbifold_ratio",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 CMB Non-Evidence Policy Gate",
        "",
        f"Z4/CMB marked non-evidence: `{payload['z4_cmb_marked_non_evidence']}`",
        f"Active core: `{payload['active_core']}`",
        "",
        "Z4/CMB attempts are diagnostic trace material, not active geometry.",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
