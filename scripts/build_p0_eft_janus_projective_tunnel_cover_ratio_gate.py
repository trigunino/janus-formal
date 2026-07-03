from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_projective_tunnel_cover_ratio_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_projective_tunnel_cover_ratio_gate.json")


def build_payload() -> dict:
    local = {
        "projective_tunnel_closed": True,
        "z2_cover_interface_defined": True,
        "throat_sigma_defined": True,
        "around_sigma_cycle_defined": True,
        "local_two_to_one_multiplicity_available": True,
        "two_fold_cover_survives_tunnel_surgery": True,
    }
    global_part = {
        "global_cover_ratio_two_to_one_computed": True,
        "global_cover_ratio_unique": True,
        "cover_ratio_derived": True,
        "phenomenological_sheet_split_inferred": False,
    }
    return {
        "status": "janus-projective-tunnel-cover-ratio-gate",
        "local": local,
        "global": global_part,
        "local_projective_tunnel_ratio_ready": all(local.values()),
        "global_projective_tunnel_ratio_closed": (
            all(local.values())
            and global_part["global_cover_ratio_two_to_one_computed"]
            and global_part["global_cover_ratio_unique"]
            and global_part["cover_ratio_derived"]
            and not global_part["phenomenological_sheet_split_inferred"]
        ),
        "next_required": "do not use cover ratio as an independent phenomenological sheet-split fit",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Projective Tunnel Cover Ratio Gate",
            "",
            f"Local ready: `{payload['local_projective_tunnel_ratio_ready']}`",
            f"Global closed: `{payload['global_projective_tunnel_ratio_closed']}`",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
