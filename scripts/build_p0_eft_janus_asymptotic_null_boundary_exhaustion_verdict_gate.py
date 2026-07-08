from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_asymptotic_null_boundary_alpha_bridge_gate import (
    build_payload as build_alpha_payload,
)
from scripts.build_p0_eft_janus_asymptotic_null_boundary_charge_derivation_gate import (
    build_payload as build_charge_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_asymptotic_null_boundary_exhaustion_verdict_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_asymptotic_null_boundary_exhaustion_verdict_gate.md"


def build_payload() -> dict[str, Any]:
    charge = build_charge_payload()
    alpha = build_alpha_payload()
    routes_audited = {
        "BMS": True,
        "Newman_Penrose": True,
        "covariant_phase_space_null_boundary": True,
    }
    return {
        "status": "janus-asymptotic-null-boundary-exhaustion-verdict-gate",
        "routes_audited": routes_audited,
        "all_routes_audited": all(routes_audited.values()),
        "boundary_mass_charge_derived": charge["boundary_mass_charge_derived"],
        "M_bridge_derived": alpha["M_bridge_derived"],
        "alpha_generated_no_fit": alpha["alpha_generated_no_fit"],
        "final_branch_status": "best_next_framework_but_missing_Janus_null_boundary_data",
        "what_this_idea_adds": [
            "It targets the correct missing object: a boundary energy generator.",
            "BMS/Wald-Zoupas/NP can define mass charges when the right null/asymptotic boundary exists.",
            "It gives a concrete bridge formula from charge to M_bridge to alpha if the charge is derived.",
        ],
        "what_is_still_missing": [
            "Janus-specific asymptotically flat null infinity or active internal null boundary",
            "boundary conditions and integrable surface charge",
            "normalization of null/time generator",
            "sector selection or quantization of the charge",
        ],
        "no_fit_alpha_generated": False,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Asymptotic/Null Boundary Exhaustion Verdict Gate",
        "",
        f"All routes audited: `{payload['all_routes_audited']}`",
        f"Boundary mass charge derived: `{payload['boundary_mass_charge_derived']}`",
        f"M_bridge derived: `{payload['M_bridge_derived']}`",
        f"No-fit alpha generated: `{payload['no_fit_alpha_generated']}`",
        f"Final branch status: `{payload['final_branch_status']}`",
        "",
        "## What This Idea Adds",
        *[f"- `{item}`" for item in payload["what_this_idea_adds"]],
        "",
        "## Still Missing",
        *[f"- `{item}`" for item in payload["what_is_still_missing"]],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
