from __future__ import annotations

import json
from pathlib import Path


OUTPUT_PATH = Path("outputs/active_z2_sigma/resolved_throat_trace_equations.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_resolved_throat_trace_equations.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_resolved_throat_trace_equations.json")


def build_payload(*, output_path: Path = OUTPUT_PATH) -> dict:
    dimension = 3
    equations = {
        "round_throat_geometry": {
            "h_ab": "R^2 q_ab",
            "K_ab_plus": "+R q_ab",
            "K_ab_minus": "-R q_ab",
            "K_plus": "3/R",
            "jump_K": "[K]=6/R",
        },
        "israel_trace": {
            "trace_left_hand_side": "h^ab [K_ab - K h_ab] = -(d-1)[K] = -12/R",
            "junction_equation": "[K_ab - K h_ab] = -kappa_Z2Sigma S_ab",
            "surface_stress_trace_target": "S = h^ab S_ab = 12/(kappa_Z2Sigma R)",
        },
        "minimal_basis": {
            "L_min": "c1*(epsilon_Z2*K) + c2*K^2 + c3*R[h]",
            "on_round_throat": "L_min = 3*c1*epsilon_Z2/R + (9*c2+6*c3)/R^2",
            "dL_dK": "c1*epsilon_Z2 + 6*c2/R",
            "R_K_q": "-3*(c1*epsilon_Z2 + 6*c2/R)/R^2",
            "R_h_q": "3*c1*epsilon_Z2/R^3 + (18*c2+6*c3)/R^4",
            "h_trace_R_h": "R^2 R_h_q = 3*c1*epsilon_Z2/R + (18*c2+6*c3)/R^2",
        },
        "dirichlet_throat_no_independent_K_variation_if_imposed": {
            "condition": "R_K_q = 0 for all R",
            "solution": "c1 = 0 and c2 = 0",
            "remaining_h_trace": "h_trace_R_h = 6*c3/R^2",
        },
        "stress_trace_matching_obstruction": {
            "target_scaling": "S ~ 1/R",
            "minimal_constant_basis_scaling_after_R_K_zero": "h_trace_R_h ~ 1/R^2",
            "conclusion": (
                "A constant-coefficient minimal density cannot match the finite-throat "
                "Israel trace for all R after removing independent K variation."
            ),
        },
    }
    payload = {
        "status": "janus-z2-sigma-resolved-throat-trace-equations",
        "active_core": "Z2_tunnel_Sigma",
        "source": "symbolic_derivation",
        "bibliography_basis": [
            "Lanczos-Israel trace junction equation",
            "GHY/Brown-York boundary stress convention",
            "Janus Z2 normal reversal at resolved Sigma throat",
        ],
        "equations": equations,
        "R_h_trace_equation_derived": True,
        "R_K_trace_equation_derived": True,
        "R_h_trace_value_ready": False,
        "R_K_trace_value_ready": False,
        "minimal_constant_basis_closes": False,
        "obstruction": (
            "The resolved Z2 throat supplies trace equations, but matching a finite "
            "Israel throat with no independent K variation requires either a "
            "non-minimal local density, an R-dependent coefficient derived from "
            "bulk/tunnel physics, or a different boundary variational ensemble."
        ),
        "next_required": [
            "derive_boundary_variational_ensemble: Dirichlet_h_only vs mixed_h_K",
            "if_Dirichlet_h_only: extend_L_ct_basis_beyond_constant_c1_c2_c3",
            "if_mixed_h_K: derive_R_K_trace_target_instead_of_setting_it_zero",
            "only_then_emit_counterterm_metric/extrinsic_residual_tensor_inputs",
        ],
        "forbidden_shortcuts": [
            "do_not_set_c3_by_fit",
            "do_not_force_E_counterterm_zero",
            "do_not_use_minimal_constant_basis_as_closed",
        ],
        "output_manifest": str(output_path),
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Resolved Throat Trace Equations",
        "",
        f"Trace equations derived: `{payload['R_h_trace_equation_derived'] and payload['R_K_trace_equation_derived']}`",
        f"Trace values ready: `{payload['R_h_trace_value_ready'] and payload['R_K_trace_value_ready']}`",
        f"Minimal constant basis closes: `{payload['minimal_constant_basis_closes']}`",
        "",
        payload["obstruction"],
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
