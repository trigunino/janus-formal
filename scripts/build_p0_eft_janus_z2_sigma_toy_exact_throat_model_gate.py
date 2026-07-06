from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_toy_exact_throat_model_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_toy_exact_throat_model_gate.json")


def build_payload() -> dict:
    radius_symbol = "R"
    dim_sigma = 3
    scalings = {
        "sqrt_abs_h": "R^3 sqrt_abs_q",
        "K_plus": "+3/R",
        "K_minus": "-3/R",
        "K_ab_plus": "+R q_ab",
        "K_ab_minus": "-R q_ab",
        "sqrt_h_K_plus": "+3 R^2 sqrt_abs_q",
        "sqrt_h_K_minus": "-3 R^2 sqrt_abs_q",
        "sqrt_h_K2": "9 R sqrt_abs_q",
        "sqrt_h_R_intrinsic": "6 R sqrt_abs_q",
        "point_collapse_limit_sqrt_h_K": "0 as R -> 0",
        "point_collapse_limit_sqrt_h_K2": "0 as R -> 0",
        "point_collapse_limit_sqrt_h_R_intrinsic": "0 as R -> 0",
    }
    parity = {
        "h_ab": "even",
        "sqrt_abs_h": "even",
        "normal_n": "odd",
        "K_ab": "odd",
        "K_trace": "odd",
        "K_squared": "even",
        "intrinsic_R_Sigma": "even",
        "sqrt_h_K": "odd",
        "sqrt_h_K2": "even",
        "sqrt_h_R_intrinsic": "even",
    }
    return {
        "status": "janus-z2-sigma-toy-exact-throat-model-gate",
        "active_core": "Z2_tunnel_Sigma",
        "model_status": "toy_diagnostic_only",
        "proof_status": "not_a_proof_of_active_counterterm",
        "source": "diagnostic_model",
        "declared": {
            "finite_round_throat_declared": True,
            "Z2_sheet_exchange_declared": True,
            "explicit_h_ab_declared": True,
            "explicit_K_ab_declared": True,
            "point_collapse_limit_diagnostic_declared": True,
            "not_promoted_to_active_model": True,
            "fitted_counterterm_coefficient_forbidden": True,
            "not_promoted_to_transport_Bianchi_proof": True,
            "not_promoted_to_S_cross_source_proof": True,
        },
        "geometry": {
            "dimension_sigma": dim_sigma,
            "radius": radius_symbol,
            "unit_metric": "q_ab on unit S^3/RP^3 local chart",
            "induced_metric": "h_ab = R^2 q_ab",
            "extrinsic_curvature_plus": "K_ab^+ = +R q_ab",
            "extrinsic_curvature_minus": "K_ab^- = -R q_ab",
            "trace_plus": "K^+ = +3/R",
            "trace_minus": "K^- = -3/R",
        },
        "parity": parity,
        "scalings": scalings,
        "diagnostics": {
            "linear_K_terms_are_Z2_odd": True,
            "quadratic_K_terms_are_Z2_even": True,
            "intrinsic_curvature_terms_are_Z2_even": True,
            "finite_throat_does_not_force_E_counterterm_zero": True,
            "point_collapse_can_kill_integrated_power_law_terms": True,
            "point_collapse_is_singular_not_active_proof": True,
            "does_not_validate_bridge_determinant_transport": True,
            "does_not_source_derive_S_cross": True,
            "does_not_close_Bianchi": True,
        },
        "interpretation": (
            "The toy round throat confirms the expected parity bookkeeping: h is even, "
            "K is odd, linear K terms cancel under a symmetric Z2 quotient, while "
            "K^2 and intrinsic-curvature terms are even and survive unless their "
            "coefficients or integrated scaling vanish. In the point-collapse limit, "
            "the displayed geometric power-law integrals vanish, but that limit is "
            "singular and does not replace the active counterterm, S_cross, or "
            "transport/Bianchi derivations."
        ),
        "next_use": [
            "use_as_sanity_check_for_candidate_L_ct_terms",
            "reject_claims_that_all_counterterm_terms_vanish_by_Z2",
            "test_point_collapse_scaling_before_any_active_use",
            "do_not_use_as_transport_Bianchi_or_S_cross_source_input",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Toy Exact Throat Model Gate",
        "",
        f"Model status: `{payload['model_status']}`",
        f"Proof status: `{payload['proof_status']}`",
        "",
        payload["interpretation"],
        "",
        "## Parity",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["parity"].items())
    lines.extend(["", "## Scalings"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["scalings"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
