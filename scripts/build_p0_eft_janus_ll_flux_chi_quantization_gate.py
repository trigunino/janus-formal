from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_chi_ll_area_flux_micro_parameter_constraint import (
    build_payload as build_micro,
)
from scripts.build_p0_eft_janus_z2_sigma_primitive_flux_law_closure_audit import (
    build_payload as build_primitive,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_ll_flux_chi_quantization_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_ll_flux_chi_quantization_gate.md"


def build_payload() -> dict[str, Any]:
    micro = build_micro()
    primitive = build_primitive()
    equations = {
        "flux_integral": "int_C F_LL = 2*pi*n/q_LL",
        "area_flux_radius": "N_gap*A_gap = 4*pi*R_s^2",
        "ll_tension": "chi_LL = -1/(8*pi*R_s)",
        "micro_constraint": "F2_0*q_LL^2 = 8*pi^2*n^2/(N_gap*A_gap)^2",
    }
    requirements = {
        "compact_LL_worldvolume_cycle": False,
        "q_LL_charge_unit_derived": False,
        "F2_0_dynamical_value_derived": False,
        "physical_area_gauge_derived": False,
        "primitive_sector_N_gap_derived": primitive["N_gap_equals_abs_n_derived"],
        "both_micro_parameters_consistent": micro["both_micro_parameters_consistent"],
    }
    ready = all(requirements.values())
    return {
        "status": "janus-ll-flux-chi-quantization-gate",
        "equations": equations,
        "requirements": requirements,
        "previous_primitive_flux_verdict": primitive["physical_statement"],
        "previous_micro_constraint_status": micro["status"],
        "what_flux_quantization_can_do": (
            "If q_LL, F2_0, area gauge, compact cycle and primitive sector are derived, "
            "it can turn chi_LL into a discrete spectrum."
        ),
        "why_not_closed": (
            "Current repo has only formal compatibility equations. It does not derive "
            "the LL gauge charge unit, worldvolume cycle, F2_0, or primitive sector law."
        ),
        "chi_LL_selected_no_fit": ready,
        "best_remaining_non_rustine_object": "derive_minimal_LL_gauge_action_L_of_F2_with_charge_unit",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus LL Flux chi_LL Quantization Gate",
        "",
        f"chi_LL selected no-fit: `{payload['chi_LL_selected_no_fit']}`",
        f"Best remaining object: `{payload['best_remaining_non_rustine_object']}`",
        "",
        "## Equations",
        *[f"- `{key}`: `{value}`" for key, value in payload["equations"].items()],
        "",
        "## Requirements",
        *[f"- `{key}`: `{value}`" for key, value in payload["requirements"].items()],
        "",
        payload["why_not_closed"],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
