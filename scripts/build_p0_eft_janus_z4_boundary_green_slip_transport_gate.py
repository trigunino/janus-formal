from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_slip_transport_kernel_gate import build_payload as build_transport_kernel


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_boundary_green_slip_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_boundary_green_slip_transport_gate.json")


def build_payload() -> dict:
    transport = build_transport_kernel()
    green_kernel_derived = False
    gate_passed = bool(
        transport["slip_source_equation_available"]
        and green_kernel_derived
    )
    return {
        "status": "janus-z4-boundary-green-slip-transport-gate",
        "slip_transport_route": "boundary_green",
        "slip_source_equation_available": transport["slip_source_equation_available"],
        "green_kernel_declared": True,
        "green_kernel_derived": green_kernel_derived,
        "retarded_causal_support": False,
        "boundary_conditions_declared": True,
        "normalization_fixed": False,
        "GR_limit_slip_zero": True,
        "no_arbitrary_homogeneous_mode": False,
        "regular_k_to_zero": False,
        "regular_large_k": False,
        "Bianchi_residual_guard": True,
        "green_kernel_finite": False,
        "boundary_jump_conditions_satisfied": False,
        "slip_value_transport_available": gate_passed,
        "deltaSlip_Z4_value_available": gate_passed,
        "deltaSlip_Z4_dot_available": gate_passed,
        "deltaPhi_Z4_reconstructed": gate_passed,
        "deltaPsi_Z4_reconstructed": gate_passed,
        "source_level_slip_regeneration_possible": gate_passed,
        "free_slip_parameter": False,
        "free_eta_ratio": False,
        "direct_Cl_patch": False,
        "raw_toy_LOS": False,
        "lambda_retuning": False,
        "planck_trial_allowed": False,
        "boundary_green_slip_transport_gate_passed": gate_passed,
        "required_next_artifact": (
            "derive a retarded, finite, normalized boundary Green kernel "
            "G_slip_Z4(k;tau,tau_prime) satisfying Janus/Z4 boundary jumps"
        ),
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Boundary Green Slip Transport Gate",
        "",
        f"Route: `{payload['slip_transport_route']}`",
        f"Green kernel derived: `{payload['green_kernel_derived']}`",
        f"Slip value transport available: `{payload['slip_value_transport_available']}`",
        f"Gate passed: `{payload['boundary_green_slip_transport_gate_passed']}`",
        f"Planck trial allowed: `{payload['planck_trial_allowed']}`",
        "",
        payload["required_next_artifact"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
