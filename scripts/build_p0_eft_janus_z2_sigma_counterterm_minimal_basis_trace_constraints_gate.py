from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_minimal_density_basis_gate import (
    build_payload as build_minimal_basis,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_minimal_basis_trace_constraints_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_minimal_basis_trace_constraints_gate.json"
)


def build_payload() -> dict:
    basis = build_minimal_basis()
    formulas = {
        "L_min": "c1*(epsilon_Z2*K) + c2*K^2 + c3*R[h]",
        "round_throat_substitution": "K=3/R, K^2=9/R^2, R[h]=6/R^2, sqrt_h=R^3 sqrt_q",
        "sqrt_h_L_min": "sqrt_q*(3*c1*epsilon_Z2*R^2 + (9*c2 + 6*c3)*R)",
        "radial_E_counterterm": "partial_R(sqrt_h L_min)=sqrt_q*(6*c1*epsilon_Z2*R + 9*c2 + 6*c3)",
        "cartan_plus_counterterm_balance": (
            "E_RSigma/sqrt_q = 6*epsilon_Z2*R/kappa_Z2Sigma "
            "+ 6*c1*epsilon_Z2*R + 9*c2 + 6*c3"
        ),
        "formal_finite_radius_solution": (
            "R_Sigma = -(9*c2 + 6*c3)/(6*epsilon_Z2*(1/kappa_Z2Sigma + c1))"
        ),
        "K_trace_constraint": "partial L_min / partial K = c1*epsilon_Z2 + 2*c2*K",
        "K_trace_round": "c1*epsilon_Z2 + 6*c2/R",
        "metric_trace_round": "not uniquely separable from radial variation without independent R_h_trace input",
    }
    coefficient_system = {
        "unknowns": ["c1", "c2", "c3"],
        "available_equations": {
            "zero_reference_or_point_limit": "does not constrain c1,c2,c3 for R->0 power laws",
            "radial_E_counterterm_zero_if_chosen": "6*c1*epsilon_Z2*R + 9*c2 + 6*c3 = 0 for all R",
            "K_trace_match": "c1*epsilon_Z2 + 6*c2/R = target_R_K_trace",
            "finite_RSigma_balance": (
                "requires active-derived c1,c2,c3 before the formal solution can "
                "be promoted to R_Sigma_solution_certificate"
            ),
        },
        "rank_if_E_counterterm_zero_all_R": 2,
        "rank_with_K_trace_target": "2_or_3_depending_on_target_function",
        "rank_without_external_trace_targets": 0,
    }
    e_zero_solution = {
        "condition": "if one imposes E_counterterm(R)=0 for all R in the toy",
        "result": {"c1": "0", "constraint": "3*c2 + 2*c3 = 0"},
        "free_parameter": "c2",
        "interpretation": "Even the strong toy condition E_counterterm=0 leaves one free coefficient.",
    }
    return {
        "status": "janus-z2-sigma-counterterm-minimal-basis-trace-constraints-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "diagnostic_reduction",
        "model_status": "toy_minimal_basis_trace_diagnostic",
        "declared": {
            "minimal_basis_imported": basis["gate_passed"],
            "round_throat_substitution_declared": True,
            "radial_variation_formula_declared": True,
            "K_trace_variation_declared": True,
            "metric_trace_under_determined_declared": True,
            "no_coefficient_fit_used": True,
        },
        "formulas": formulas,
        "coefficient_system": coefficient_system,
        "E_counterterm_zero_toy_solution": e_zero_solution,
        "solvability": {
            "coefficients_fully_determined_by_minimal_basis": False,
            "reason": "trace_targets_missing_and_E_zero_toy_condition_under_determines_coefficients",
            "minimum_new_inputs_needed": [
                "target_R_K_trace_function_or_boundary_condition",
                "target_R_h_trace_function_or_boundary_condition",
            ],
        },
        "interpretation": (
            "The minimal basis can be varied explicitly. However, the toy round-throat "
            "scaling does not determine c1,c2,c3. Even imposing E_counterterm=0 for "
            "all R only gives c1=0 and 3*c2+2*c3=0, leaving one free parameter. "
            "The Cartan-GHY plus counterterm balance gives a formal finite R_Sigma "
            "solution, but it remains non-promotable until c1,c2,c3 are derived from "
            "active trace residual data."
        ),
        "next_required": [
            "derive_active_R_K_trace_target",
            "derive_active_R_h_trace_target",
            "then_solve_minimal_basis_coefficients",
            "then_promote_formal_finite_radius_solution_if_residual_zero",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Minimal Basis Trace Constraints Gate",
        "",
        f"Status: `{payload['model_status']}`",
        f"Fully determined: `{payload['solvability']['coefficients_fully_determined_by_minimal_basis']}`",
        "",
        payload["interpretation"],
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
