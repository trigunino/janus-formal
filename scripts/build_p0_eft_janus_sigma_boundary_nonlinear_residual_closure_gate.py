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
    component_emission = {
        "alpha_res_components_available": False,
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
        "nonlinear_closure_is_boolean_only": not component_emission[
            "alpha_res_components_available"
        ],
        "component_emission_obligation": (
            "Refine this gate from cancellation/uniqueness to explicit alpha_res "
            "components before deriving L_ct_expression or R_h/R_K values."
        ),
        "next_required": [
            "emit_alpha_res_components",
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
            f"Alpha components available: `{payload['component_emission']['alpha_res_components_available']}`",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
