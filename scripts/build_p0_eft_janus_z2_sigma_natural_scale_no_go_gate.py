from __future__ import annotations

import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_action_scale_inventory_gate import (
    build_payload as build_action_scale_inventory,
)

G_PATH = Path("outputs/active_z2_sigma/background_gravity_normalization_inputs.json")
CONSTANTS_PATH = Path("outputs/active_z2_sigma/early_plasma_codata_constants_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_natural_scale_no_go_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_natural_scale_no_go_gate.json")

C_SI = 299_792_458.0


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload(
    *,
    g_path: Path = G_PATH,
    constants_path: Path = CONSTANTS_PATH,
) -> dict:
    gravity = _read(g_path)
    constants = _read(constants_path)
    action_inventory = build_action_scale_inventory()
    g_value = gravity.get("scalars", {}).get("gravitational_constant_si_Z2Sigma")
    hbar = constants.get("constants", {}).get("hbar_J_s")
    planck_length_m = None
    if g_value is not None and hbar is not None:
        planck_length_m = math.sqrt(float(hbar) * float(g_value) / C_SI**3)
    closure = {
        "G_SI_available": g_value is not None,
        "hbar_SI_available": hbar is not None,
        "c_SI_exact_available": True,
        "natural_planck_length_constructible": planck_length_m is not None,
        "janus_action_identifies_RSigma_with_planck_length": False,
        "janus_action_identifies_collar_with_planck_length": False,
        "dimensionless_coupling_selects_scale": False,
    }
    return {
        "status": "janus-z2-sigma-natural-scale-no-go-gate",
        "active_core": "Z2_tunnel_Sigma",
        "candidate_natural_scale": {
            "name": "Planck_length",
            "formula": "sqrt(hbar*G/c^3)",
            "value_m": planck_length_m,
        },
        "action_scale_inventory": {
            "status": action_inventory["status"],
            "any_action_scale_available": action_inventory["any_action_scale_available"],
            "absolute_RSigma_from_action_ready": action_inventory[
                "absolute_RSigma_from_action_ready"
            ],
        },
        "closure": closure,
        "natural_scale_constructible": bool(planck_length_m),
        "natural_scale_accepted_as_RSigma": False,
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "interpretation": (
            "CODATA constants allow construction of a Planck length, but the active "
            "Janus/Z2/Sigma model has no theorem or action term identifying that "
            "length with R_Sigma or the collar scale. Using it as the throat scale "
            "would be an extra postulate."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Natural Scale No-Go Gate",
        "",
        payload["interpretation"],
        "",
        f"Planck length constructible: `{payload['natural_scale_constructible']}`",
        f"Accepted as R_Sigma: `{payload['natural_scale_accepted_as_RSigma']}`",
        f"Planck length value m: `{payload['candidate_natural_scale']['value_m']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
