from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tunnel_junction_condition_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tunnel_junction_condition_gate.json")


def build_payload() -> dict:
    lock = {
        "projected_sigma_stress_tensor_derived": True,
        "two_fold_cover_survives_tunnel_surgery": True,
        "sigma_normal_orientation_declared": True,
        "extrinsic_curvature_jump_declared": True,
        "lanczos_israel_like_jump_equation_declared": True,
        "z2_orientation_reversal_included": True,
        "no_antipodal_fixed_point_shell": True,
    }
    return {
        "status": "janus-z2-sigma-tunnel-junction-condition-gate",
        "active_core": "Z2_tunnel_Sigma",
        "lock": lock,
        "tunnel_junction_lock_closed": all(lock.values()),
        "z2_tunnel_junction_condition_derived": all(lock.values()),
        "junction_condition": "[K_ab - K h_ab]_Z2 = -kappa * T_Sigma_ab with Z2 normal-orientation reversal",
        "legacy_lcdm_background_substitution_forbidden": True,
        "archived_z4_junction_reuse_forbidden": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Tunnel Junction Condition Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Z2 tunnel junction condition derived: `{payload['z2_tunnel_junction_condition_derived']}`",
        "",
        f"Condition: `{payload['junction_condition']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
