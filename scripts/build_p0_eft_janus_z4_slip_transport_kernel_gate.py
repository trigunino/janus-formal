from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_traceless_spatial_slip_equation_gate import build_payload as build_equation


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_slip_transport_kernel_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_slip_transport_kernel_gate.json")


def build_payload() -> dict:
    equation = build_equation()
    boundary_green_kernel_derived = False
    normal_mode_transport_derived = False
    transport_available = bool(
        equation["slip_equation_gate_passed"]
        and (boundary_green_kernel_derived or normal_mode_transport_derived)
    )
    return {
        "status": "janus-z4-slip-transport-kernel-gate",
        "slip_source_equation_available": bool(equation["slip_equation_gate_passed"]),
        "acceptable_routes": ["boundary_green_transport", "normal_mode_transport"],
        "boundary_green_kernel_derived": boundary_green_kernel_derived,
        "normal_mode_transport_derived": normal_mode_transport_derived,
        "slip_value_transport_available": transport_available,
        "deltaSlip_Z4_value_available": transport_available,
        "deltaSlip_Z4_dot_available": transport_available,
        "deltaPhi_Z4_reconstructed": transport_available,
        "deltaPsi_Z4_reconstructed": transport_available,
        "source_level_regeneration_possible": transport_available,
        "free_slip_parameter": False,
        "free_eta_ratio": False,
        "boundary_conditions_declared": True,
        "normalization_fixed": False,
        "GR_limit_slip_zero": True,
        "Bianchi_residual_checked": True,
        "gauge_convention_declared": True,
        "superhorizon_regular": False,
        "subhorizon_regular": False,
        "no_exploding_homogeneous_mode": False,
        "no_singular_denominator": True,
        "no_gauge_artifact_mode": False,
        "no_boundary_discontinuity": False,
        "no_unphysical_sign_flip_at_TCA_switch": False,
        "green_kernel_finite": False,
        "retarded_support": False,
        "boundary_jump_conditions_satisfied": False,
        "eigenvalues_finite": False,
        "mode_basis_invertible": False,
        "projection_matrix_nonsingular": False,
        "no_direct_Cl_patch": True,
        "raw_toy_LOS_forbidden": True,
        "planck_trial_forbidden": True,
        "transport_kernel_gate_passed": False,
        "required_next_artifact": (
            "derive either a causal normalized boundary Green kernel or a regular "
            "normal-mode transport from S_slip_Z4 to deltaSlip_Z4(k,tau)"
        ),
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Slip Transport Kernel Gate",
        "",
        f"Slip source equation available: `{payload['slip_source_equation_available']}`",
        f"Slip value transport available: `{payload['slip_value_transport_available']}`",
        f"Transport kernel gate passed: `{payload['transport_kernel_gate_passed']}`",
        f"Planck trial forbidden: `{payload['planck_trial_forbidden']}`",
        "",
        payload["required_next_artifact"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
