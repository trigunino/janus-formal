from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.write_p0_eft_janus_z2_sigma_dimensionless_noether_density_from_charge import (
    build_payload as build_dimensionless_density_payload,
)
from scripts.write_p0_eft_janus_z2_sigma_hubble_volume_noether_density import (
    build_payload as build_hubble_density_payload,
)
from scripts.write_p0_eft_janus_z2_sigma_projected_charge_from_occupation_state import (
    build_payload as build_charge_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_state_density_chain.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_state_density_chain.json")


def build_payload() -> dict:
    charge = build_charge_payload()
    density = build_dimensionless_density_payload()
    hubble_density = build_hubble_density_payload()
    passed = charge["gate_passed"] and density["gate_passed"] and hubble_density["gate_passed"]
    primary_blocker = (
        "none"
        if passed
        else charge["primary_blocker"]
        if not charge["gate_passed"]
        else density["primary_blocker"]
        if not density["gate_passed"]
        else hubble_density["primary_blocker"]
    )
    return {
        "status": "janus-z2-sigma-effective-state-density-chain",
        "active_core": "Z2_tunnel_Sigma",
        "charge_from_occupation": charge,
        "dimensionless_noether_density": density,
        "hubble_volume_noether_density": hubble_density,
        "chain_passed": passed,
        "full_no_fit_prediction_ready": False,
        "primary_blocker": primary_blocker,
        "next_required": [
            "supply_or_derive_projected_occupation_state_inputs_json",
            "derive_H0_Z2Sigma_or_R_curv_Z2Sigma_m_for_SI_density",
            "feed_SI_baryon_density_to_Saha_Thomson_plasma",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Effective-State Density Chain",
                "",
                f"Charge from occupation: `{payload['charge_from_occupation']['gate_passed']}`",
                f"Dimensionless Noether density: `{payload['dimensionless_noether_density']['gate_passed']}`",
                f"Hubble-volume Noether density: `{payload['hubble_volume_noether_density']['gate_passed']}`",
                f"Chain passed: `{payload['chain_passed']}`",
                f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
                f"Primary blocker: `{payload['primary_blocker']}`",
                "",
                "## Next Required",
                *[f"- `{item}`" for item in payload["next_required"]],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
