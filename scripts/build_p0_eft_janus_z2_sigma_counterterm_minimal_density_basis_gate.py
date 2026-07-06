from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_toy_exact_throat_model_gate import (
    build_payload as build_toy_model,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_minimal_density_basis_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_minimal_density_basis_gate.json"
)


def build_payload() -> dict:
    toy = build_toy_model()
    candidate_terms = [
        {
            "name": "constant",
            "symbol": "1",
            "z2_parity": "even",
            "kept": False,
            "reason": "removed_by_L_ct_reference_zero_throat_normalization",
        },
        {
            "name": "linear_K",
            "symbol": "epsilon_Z2 * K",
            "z2_parity": "even_density_from_orientation_times_odd_K",
            "kept": True,
            "reason": "minimal orientation-sensitive throat term; independent of GHY only as residual counterterm slot",
        },
        {
            "name": "K_squared",
            "symbol": "K_ab K^ab or K^2",
            "z2_parity": "even",
            "kept": True,
            "reason": "survives finite throat Z2 quotient in toy model",
        },
        {
            "name": "intrinsic_curvature",
            "symbol": "R[h]",
            "z2_parity": "even",
            "kept": True,
            "reason": "intrinsic Sigma curvature survives finite throat Z2 quotient",
        },
        {
            "name": "torsion_pullback_square",
            "symbol": "T_A T^A",
            "z2_parity": "even",
            "kept": False,
            "reason": "zero on active torsionless Sigma branch; keep for non-torsionless extension only",
        },
        {
            "name": "immirzi_radion_gradient",
            "symbol": "(D chi)^2 or n(chi)",
            "z2_parity": "open",
            "kept": False,
            "reason": "full R_chi component parity not available; excluded from minimal torsionless basis",
        },
    ]
    kept_terms = [term for term in candidate_terms if term["kept"]]
    unknown_coefficients = [f"c_{term['name']}" for term in kept_terms]
    constraints = {
        "zero_reference_throat": "L_ct(reference_residual_zero_throat)=0",
        "cancel_metric_residual_trace": "variation wrt h_ab matches R_h trace",
        "cancel_extrinsic_residual_trace": "variation wrt K_ab matches R_K trace",
    }
    independent_constraints_available = {
        "zero_reference_throat": True,
        "cancel_metric_residual_trace": False,
        "cancel_extrinsic_residual_trace": False,
    }
    coefficient_count = len(unknown_coefficients)
    available_constraint_count = sum(independent_constraints_available.values())
    solvable_now = available_constraint_count >= coefficient_count and all(
        independent_constraints_available.values()
    )
    return {
        "status": "janus-z2-sigma-counterterm-minimal-density-basis-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "diagnostic_reduction",
        "model_status": "minimal_basis_diagnostic_not_active_L_ct_solution",
        "declared": {
            "toy_exact_model_imported": toy["gate_passed"],
            "locality_restriction_declared": True,
            "dimension_low_order_restriction_declared": True,
            "Z2_parity_filter_declared": True,
            "torsionless_branch_filter_declared": True,
            "normalization_removes_constant_declared": True,
            "fitted_coefficients_forbidden": True,
        },
        "candidate_terms": candidate_terms,
        "minimal_basis": {
            "kept_terms": [term["name"] for term in kept_terms],
            "unknown_coefficients": unknown_coefficients,
            "basis_size": coefficient_count,
            "basis_expression": "c_linear_K*(epsilon_Z2 K) + c_K_squared*K2 + c_intrinsic_curvature*R[h]",
        },
        "constraints": constraints,
        "independent_constraints_available": independent_constraints_available,
        "solvability": {
            "unknown_coefficient_count": coefficient_count,
            "available_constraint_count": available_constraint_count,
            "coefficient_system_solvable_now": solvable_now,
            "primary_blocker": "R_h_trace_and_R_K_trace_constraints",
        },
        "interpretation": (
            "The minimal finite-throat torsionless basis is small: linear K, K^2, "
            "and intrinsic curvature. It is still not solvable from symmetry alone. "
            "The zero-throat normalization gives one constraint, but the metric and "
            "extrinsic residual trace constraints must be supplied from alpha_res "
            "component values or an explicit residual equation."
        ),
        "next_required": [
            "derive_R_h_trace_constraint_on_minimal_basis",
            "derive_R_K_trace_constraint_on_minimal_basis",
            "then_solve_for_c_linear_K_c_K_squared_c_intrinsic_curvature",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Minimal Density Basis Gate",
        "",
        f"Status: `{payload['model_status']}`",
        f"Basis: `{payload['minimal_basis']['basis_expression']}`",
        f"Solvable now: `{payload['solvability']['coefficient_system_solvable_now']}`",
        "",
        payload["interpretation"],
        "",
        "## Terms",
    ]
    for term in payload["candidate_terms"]:
        lines.append(
            f"- `{term['name']}`: kept=`{term['kept']}`, parity=`{term['z2_parity']}`"
        )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
