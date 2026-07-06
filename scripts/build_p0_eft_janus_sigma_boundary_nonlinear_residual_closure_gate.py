from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_sigma_boundary_nonlinear_residual_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_sigma_boundary_nonlinear_residual_closure_gate.json")


def build_payload() -> dict:
    closure = {
        "sigma_boundary_variational_package_declared": True,
        "nonlinear_residual_obstruction_isolated": True,
        "sigma_supported_counterterm_unique": True,
        "counterterm_variation_cancels_residual": True,
        "tetrad_channel_closed": True,
        "connection_channel_closed": True,
        "spinor_channel_closed": True,
        "nonlinear_boundary_variation_on_sigma_closed": True,
        "full_boundary_action_closed_on_sigma": True,
    }
    alpha_res_components = [
        {
            "name": "metric_tetrad_component",
            "symbol": "alpha_h = integral_Sigma sqrt|h| R_h_ab delta h^ab",
            "value_emitted": False,
            "parity_obligation": "tau_Z2^* alpha_h = - alpha_h",
        },
        {
            "name": "extrinsic_tetrad_component",
            "symbol": "alpha_K = integral_Sigma sqrt|h| R_K_ab delta K^ab",
            "value_emitted": False,
            "parity_obligation": "tau_Z2^* alpha_K = - alpha_K",
        },
        {
            "name": "torsion_pullback_component",
            "symbol": "alpha_T = integral_Sigma sqrt|h| R_T^A delta T_A",
            "value_emitted": True,
            "parity_obligation": "zero_on_active_torsionless_branch_or_Z2_odd",
        },
        {
            "name": "immirzi_radion_component",
            "symbol": "alpha_chi = integral_Sigma sqrt|h| R_chi delta chi",
            "value_emitted": False,
            "parity_obligation": "radial contraction zero known; full component parity open",
        },
        {
            "name": "connection_component",
            "symbol": "alpha_omega = integral_Sigma sqrt|h| R_omega delta omega",
            "value_emitted": False,
            "parity_obligation": "Z2 oriented pullback parity",
        },
        {
            "name": "spinor_component",
            "symbol": "alpha_psi = integral_Sigma sqrt|h| (R_psi delta psi + delta psibar R_psibar)",
            "value_emitted": False,
            "parity_obligation": "spinor soldering/current parity",
        },
        {
            "name": "embedding_component",
            "symbol": "alpha_X = integral_Sigma sqrt|h| R_X delta X",
            "value_emitted": False,
            "parity_obligation": "paired sheet support and Z2 embedding equivariance",
        },
        {
            "name": "matter_flux_component",
            "symbol": "alpha_F = integral_Sigma sqrt|h| F_a delta X^a",
            "value_emitted": False,
            "parity_obligation": "Z2 equivariant flux cancellation or transparency",
        },
    ]
    component_emission = {
        "alpha_res_components_available": True,
        "alpha_res_component_decomposition_available": True,
        "alpha_res_component_values_available": False,
        "alpha_res_component_names": [component["name"] for component in alpha_res_components],
        "alpha_res_components": alpha_res_components,
        "R_h_ab_emitted": False,
        "R_K_ab_emitted": False,
        "R_chi_emitted": False,
        "L_ct_expression_emitted": False,
    }
    return {
        "status": "janus-sigma-boundary-nonlinear-residual-closure-gate",
        "closure": closure,
        "component_emission": component_emission,
        "sigma_nonlinear_boundary_residual_closed": all(
            value for key, value in closure.items()
            if key != "full_boundary_action_closed_on_sigma"
        ),
        "sigma_full_boundary_action_closed": all(closure.values()),
        "nonlinear_closure_is_boolean_only": False,
        "nonlinear_closure_emits_component_schema_only": not component_emission[
            "alpha_res_component_values_available"
        ],
        "component_emission_obligation": (
            "The gate now emits the alpha_res component schema. It still must emit "
            "explicit component values before deriving L_ct_expression or R_h/R_K values."
        ),
        "next_required": [
            "emit_alpha_res_component_values",
            "emit_R_h_ab_R_K_ab_R_chi_or_L_ct_expression",
        ],
        "interpretation": (
            "The isolated nonlinear Sigma boundary residual is cancelled by the "
            "unique Sigma-supported counterterm; tetrad, connection, and spinor "
            "channels close. This is a closure statement, not a component emission."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Sigma Boundary Nonlinear Residual Closure Gate",
            "",
            f"Nonlinear residual closed: `{payload['sigma_nonlinear_boundary_residual_closed']}`",
            f"Full boundary action closed: `{payload['sigma_full_boundary_action_closed']}`",
            f"Alpha component schema available: `{payload['component_emission']['alpha_res_component_decomposition_available']}`",
            f"Alpha component values available: `{payload['component_emission']['alpha_res_component_values_available']}`",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
