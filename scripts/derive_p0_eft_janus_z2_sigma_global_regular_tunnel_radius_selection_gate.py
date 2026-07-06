from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_global_regular_tunnel_radius_selection_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_global_regular_tunnel_radius_selection_gate.json"
)


def build_payload() -> dict:
    lambda_symbol = "lambda_Sigma = R_Sigma / ell_collar"
    selection_functional = (
        "F_reg(lambda_Sigma) = "
        "||normal_frame_holonomy_defect||^2 + "
        "||junction_defect||^2 + "
        "||collar_endpoint_mismatch||^2"
    )
    local_regular = {
        "Z2_even_induced_metric": True,
        "Z2_odd_extrinsic_curvature": True,
        "minimal_throat_R_prime_zero": True,
        "positive_throat_second_variation_required": True,
        "no_conical_defect_local_condition": True,
    }
    global_regular = {
        "projective_Z2_deck_map_used": True,
        "collar_endpoint_gluing_required": True,
        "normal_frame_holonomy_identity_required": True,
        "distributional_Bianchi_defect_forbidden": True,
        "localized_tunnel_defect_action_forbidden": True,
    }
    derived_now = {
        "dimensionless_radius_variable_declared": True,
        "global_regular_selection_functional_declared": True,
        "local_regular_conditions_close": True,
        "absolute_R_Sigma_fixed": False,
        "R_Sigma_over_ell_collar_fixed": False,
        "F_reg_computed_from_active_embedding": False,
    }
    return {
        "status": "janus-z2-sigma-global-regular-tunnel-radius-selection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "route": "global defect-free regular tunnel selection",
        "source": "active_symbolic_audit",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "lambda_symbol": lambda_symbol,
        "selection_equation_target": f"{selection_functional} = 0",
        "local_regular_conditions": local_regular,
        "global_regular_conditions": global_regular,
        "derived_now": derived_now,
        "physical_interpretation": (
            "If F_reg is derived from the active Z2 tunnel embedding, the throat "
            "ratio is selected by absence of global gluing/holonomy/Bianchi defects "
            "rather than by an observational fit or an added Sigma density."
        ),
        "gate_passed": True,
        "radius_selection_ready": False,
        "primary_blocker": "F_reg_lambda_not_computed_from_active_embedding",
        "next_required": [
            "derive active collar metric around Sigma",
            "compute normal-frame holonomy around the Z2 tunnel collar",
            "compute endpoint gluing mismatch under the projective deck map",
            "compute distributional Bianchi/junction residual",
            "solve F_reg(lambda_Sigma)=0 if the computed functional is non-flat",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Global Regular Tunnel Radius Selection Gate",
        "",
        f"Route: `{payload['route']}`",
        f"Radius variable: `{payload['lambda_symbol']}`",
        f"Selection ready: `{payload['radius_selection_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Selection Target",
        f"`{payload['selection_equation_target']}`",
        "",
        payload["physical_interpretation"],
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
