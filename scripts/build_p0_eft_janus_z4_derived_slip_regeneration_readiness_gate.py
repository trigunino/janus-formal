from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_traceless_spatial_slip_equation_gate import build_payload as build_equation


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_regeneration_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_regeneration_readiness_gate.json")


def build_payload() -> dict:
    equation = build_equation()
    ready = bool(equation["slip_equation_gate_passed"] and equation["value_slip_transport_closed"])
    return {
        "status": "janus-z4-derived-slip-regeneration-readiness-gate",
        "slip_equation_gate_passed": equation["slip_equation_gate_passed"],
        "value_slip_transport_closed": equation["value_slip_transport_closed"],
        "boundary_green_or_normal_mode_required": not equation["value_slip_transport_closed"],
        "deltaSlip_Z4_regenerated_per_cosmology": ready,
        "deltaPhi_Z4_regenerated_per_cosmology": ready,
        "deltaPsi_Z4_regenerated_per_cosmology": ready,
        "temperature_source_regenerated_with_slip": ready,
        "Pi_source_regenerated_with_slip": ready,
        "carrier_tangent_projection_required_before_planck_trial": True,
        "derived_slip_regeneration_ready": ready,
        "planck_trial_allowed": False,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Derived Slip Regeneration Readiness Gate",
        "",
        f"Derived slip regeneration ready: `{payload['derived_slip_regeneration_ready']}`",
        f"Boundary Green/normal-mode required: `{payload['boundary_green_or_normal_mode_required']}`",
        f"Planck trial allowed: `{payload['planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
