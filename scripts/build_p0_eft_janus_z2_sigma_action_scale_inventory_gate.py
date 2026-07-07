from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_schwarzschild_pt_bridge_scale_gate import (
    build_payload as build_schwarzschild_scale,
)

BASE = Path("outputs/active_z2_sigma")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_action_scale_inventory_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_action_scale_inventory_gate.json")


INPUTS = {
    "gravity": BASE / "background_gravity_normalization_inputs.json",
    "holst_components": BASE / "holst_nieh_yan_components.json",
    "holst_radial": BASE / "rsigma_E_HolstNiehYan.json",
    "counterterm_obstruction": BASE / "counterterm_local_density_action_obstruction.json",
    "time_gauge_leaf_action": BASE / "time_gauge_leaf_action_inputs.json",
}


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload() -> dict:
    data = {name: _read(path) for name, path in INPUTS.items()}
    schwarzschild = build_schwarzschild_scale()
    holst_values = data["holst_radial"].get("term_values", [])
    routes = {
        "einstein_hilbert_gravity_G": {
            "available": bool(
                data["gravity"].get("scalars", {}).get("gravitational_constant_si_Z2Sigma")
            ),
            "fixes_length_by_itself": False,
            "reason": "G fixes coupling units, not a classical solution length without mass, Lambda, or boundary state.",
        },
        "holst_nieh_yan": {
            "available": bool(data["holst_components"]),
            "fixes_length_by_itself": False,
            "reason": "Current active torsionless branch gives zero Holst/Nieh-Yan radial energy.",
            "term_values": holst_values,
        },
        "explicit_sigma_counterterm": {
            "available": False,
            "fixes_length_by_itself": False,
            "reason": data["counterterm_obstruction"].get(
                "obstruction",
                "No active counterterm action inventory found.",
            ),
        },
        "time_gauge_leaf_action": {
            "available": bool(data["time_gauge_leaf_action"]),
            "fixes_length_by_itself": False,
            "reason": "Time leaf action fixes parity/foliation branch, not physical seconds or length.",
        },
        "cosmological_constant_or_potential": {
            "available": False,
            "fixes_length_by_itself": False,
            "reason": "No active Lambda, scalar potential, tension, or mass scale manifest is present.",
        },
        "schwarzschild_PT_bridge_Rs": {
            "available": schwarzschild["closure"]["RSigma_over_Rs_fixed"],
            "fixes_length_by_itself": schwarzschild[
                "absolute_RSigma_from_schwarzschild_bridge_ready"
            ],
            "reason": "R_Sigma/R_s is fixed, but R_s requires a mass/charge and the active PT throat is null for the regular h,K pipeline.",
        },
    }
    return {
        "status": "janus-z2-sigma-action-scale-inventory-gate",
        "active_core": "Z2_tunnel_Sigma",
        "routes": routes,
        "any_action_scale_available": any(
            route["available"] and route["fixes_length_by_itself"]
            for route in routes.values()
        ),
        "absolute_RSigma_from_action_ready": False,
        "blocked_by": [
            name
            for name, route in routes.items()
            if not (route["available"] and route["fixes_length_by_itself"])
        ],
        "interpretation": (
            "The active action inventory contains coupling conventions and "
            "topological/boundary zero channels, but no dimensionful action term "
            "that selects the absolute Sigma throat scale."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Action Scale Inventory Gate",
        "",
        payload["interpretation"],
        "",
        f"Any action scale available: `{payload['any_action_scale_available']}`",
        f"Absolute R_Sigma from action ready: `{payload['absolute_RSigma_from_action_ready']}`",
        "",
        "## Routes",
    ]
    lines.extend(
        f"- `{name}`: available=`{route['available']}`, fixes_length=`{route['fixes_length_by_itself']}`"
        for name, route in payload["routes"].items()
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
