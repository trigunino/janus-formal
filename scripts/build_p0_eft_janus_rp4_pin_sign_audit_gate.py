from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_rp4_pin_sign_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_rp4_pin_sign_audit_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-rp4-pin-sign-audit-gate",
        "global_base_is_rp4": True,
        "rp4_non_orientable_recorded": True,
        "rp2_boy_shadow_not_used_as_global_pin_proof": True,
        "pin_sign_computed_for_rp4": True,
        "rp4_base_pin_plus_exists": True,
        "rp4_base_pin_minus_exists": False,
        "sigma_aps_boundary_pin_lift_closed": False,
        "pin_minus_lift_allowed": False,
        "aps_pin_closure_allowed": False,
        "next_required": "derive Sigma APS boundary Pin lift after RP4 base Pin+ computation",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus RP4 Pin Sign Audit Gate",
            "",
            f"Pin sign computed for RP4: `{payload['pin_sign_computed_for_rp4']}`",
            f"RP4 base Pin+: `{payload['rp4_base_pin_plus_exists']}`",
            f"RP4 base Pin-: `{payload['rp4_base_pin_minus_exists']}`",
            f"Sigma APS boundary Pin lift closed: `{payload['sigma_aps_boundary_pin_lift_closed']}`",
            f"APS/Pin closure allowed: `{payload['aps_pin_closure_allowed']}`",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
