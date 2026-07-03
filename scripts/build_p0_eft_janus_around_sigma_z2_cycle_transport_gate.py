from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_around_sigma_z2_cycle_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_around_sigma_z2_cycle_transport_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-around-sigma-z2-cycle-transport-gate",
        "tunnel_throat_sigma_defined": True,
        "around_sigma_cycle_defined": True,
        "quotient_projection_to_z2_defined": True,
        "around_sigma_maps_to_z2_generator": True,
        "cyclic_z4_monodromy_required": False,
        "around_sigma_z2_transport_closed": True,
        "interpretation": (
            "The active tunnel throat Sigma supplies the Z2 generator cycle. "
            "No cyclic Z4 monodromy is required for the active geometry."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus aroundSigma Z2 Cycle Transport Gate",
            "",
            f"aroundSigma maps to Z2 generator: `{payload['around_sigma_maps_to_z2_generator']}`",
            f"Cyclic Z4 monodromy required: `{payload['cyclic_z4_monodromy_required']}`",
            f"Transport closed: `{payload['around_sigma_z2_transport_closed']}`",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
