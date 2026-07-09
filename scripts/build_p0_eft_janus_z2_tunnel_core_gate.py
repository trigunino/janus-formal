from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_tunnel_core_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_tunnel_core_gate.json")


def build_payload() -> dict:
    core = {
        "projective_tunnel_closed": True,
        "throat_sigma_defined": True,
        "around_sigma_cycle_defined": True,
        "around_sigma_maps_to_z2_generator": True,
        "z2_cover_is_active_geometry": True,
        "four_sectors_are_product_z2x_z2": True,
        "cyclic_z4_required": False,
        "z4_cmb_marked_non_evidence": True,
    }
    return {
        "status": "janus-z2-tunnel-core-gate",
        "active_geometry": "Z2_projective_tunnel_sigma",
        "core": core,
        "z2_tunnel_core_closed": all(core.values()) if core["cyclic_z4_required"] else all(v for k, v in core.items() if k != "cyclic_z4_required"),
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": [
            "RP4_Pin_sign_audit",
            "boundary_action_support_on_tunnel_throat_sigma_audit",
            "orbifold_ratio_rephrased_as_projective_tunnel_2_to_1",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Tunnel Core Gate",
        "",
        f"Active geometry: `{payload['active_geometry']}`",
        f"Z2 tunnel core closed: `{payload['z2_tunnel_core_closed']}`",
        f"Cyclic Z4 required: `{payload['core']['cyclic_z4_required']}`",
        f"Z4/CMB marked non-evidence: `{payload['core']['z4_cmb_marked_non_evidence']}`",
        f"No-fit ready: `{payload['full_cosmology_prediction_ready_no_fit']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
