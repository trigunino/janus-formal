from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_boundary_green_slip_transport_gate import build_payload as build_green_transport


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_boundary_green_operator_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_boundary_green_operator_closure_gate.json")


def build_payload() -> dict:
    green_transport = build_green_transport()
    operator_declared = bool(green_transport["slip_source_equation_available"])
    operator_type = "boundary_normal"
    kernel_derived = False
    return {
        "status": "janus-z4-boundary-green-operator-closure-gate",
        "green_operator_type": operator_type,
        "L_slip_Z4_declared": operator_declared,
        "operator_domain_declared": True,
        "operator_source_declared": True,
        "boundary_conditions_declared": True,
        "Green_solves_operator_equation": kernel_derived,
        "operator_equation": "L_slip_Z4 G_slip_Z4(k;x,x_prime) = delta(x-x_prime)",
        "boundary_condition_form": "B_Z4[G]=0 plus possible boundary jump rows",
        "boundary_jump_conditions_satisfied": False,
        "normalization_fixed": False,
        "homogeneous_mode_policy": "unresolved",
        "homogeneous_mode_removed_or_fixed": False,
        "GR_limit_slip_zero": True,
        "k_zero_regular": False,
        "large_k_regular": False,
        "Bianchi_residual_guard": True,
        "gauge_convention_declared": True,
        "retarded_support_required": False,
        "no_acausal_time_dependence_introduced": True,
        "free_slip_amplitude": False,
        "free_eta_ratio": False,
        "manual_deltaSlip_table": False,
        "direct_Cl_patch": False,
        "Planck_trial": False,
        "green_kernel_derived": kernel_derived,
        "deltaSlip_value_transport_available": False,
        "deltaSlipDot_Z4_available": False,
        "operator_closure_gate_passed": False,
        "required_next_artifact": (
            "derive the boundary-normal Green kernel satisfying L_slip_Z4 G=delta, "
            "Z4 boundary jumps, fixed normalization, and regular k limits"
        ),
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Boundary Green Operator Closure Gate",
        "",
        f"Operator type: `{payload['green_operator_type']}`",
        f"L_slip_Z4 declared: `{payload['L_slip_Z4_declared']}`",
        f"Green solves operator equation: `{payload['Green_solves_operator_equation']}`",
        f"Normalization fixed: `{payload['normalization_fixed']}`",
        f"Homogeneous mode policy: `{payload['homogeneous_mode_policy']}`",
        f"Gate passed: `{payload['operator_closure_gate_passed']}`",
        "",
        payload["required_next_artifact"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
