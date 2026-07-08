from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_asymptotic_null_boundary_charge_derivation_gate import (
    build_payload as build_charge_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_asymptotic_null_boundary_alpha_bridge_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_asymptotic_null_boundary_alpha_bridge_gate.md"


def build_payload() -> dict[str, Any]:
    charge = build_charge_payload()
    conditional_map = {
        "if_boundary_mass_charge_Q_exists": "M_bridge = Q/c^2",
        "alpha_relation": "alpha_m = -2*pi*G*M_bridge/c^2",
        "ll_bridge_relation": "R_s = 2*G*M_bridge/c^2 and chi_LL = -1/(8*pi*R_s)",
    }
    return {
        "status": "janus-asymptotic-null-boundary-alpha-bridge-gate",
        "boundary_mass_charge_ready": charge["boundary_mass_charge_derived"],
        "conditional_map": conditional_map,
        "M_bridge_derived": False,
        "alpha_generated_no_fit": False,
        "sector_selection_or_quantization_derived": False,
        "blocked_by": [
            "boundary_mass_charge_not_derived",
            "time_generator_or_reference_not_selected",
            "sector_selection_or_quantization_not_derived",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Asymptotic/Null Boundary Alpha Bridge Gate",
        "",
        f"Boundary mass charge ready: `{payload['boundary_mass_charge_ready']}`",
        f"M_bridge derived: `{payload['M_bridge_derived']}`",
        f"Alpha generated no-fit: `{payload['alpha_generated_no_fit']}`",
        "",
        "## Conditional Map",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["conditional_map"].items())
    lines.extend(["", "## Blocked By"])
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
