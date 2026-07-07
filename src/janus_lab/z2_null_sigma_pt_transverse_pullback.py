"""PT pullback of transverse curvature for the Janus null Sigma bridge."""

from __future__ import annotations

from src.janus_lab.z2_null_sigma_barrabes_israel import (
    null_sigma_barrabes_israel_payload,
)


def null_sigma_pt_transverse_pullback_payload(rs: float = 1.0) -> dict:
    if rs <= 0.0:
        raise ValueError("rs must be positive")

    bi = null_sigma_barrabes_israel_payload(rs)
    c_plus = bi["transverse_curvature_plus_side"]
    c_minus = {
        "C_TT": -c_plus["C_TT"],
        "C_theta_theta_over_unit_sphere": -c_plus[
            "C_theta_theta_over_unit_sphere"
        ],
        "C_phi_phi_over_sin2theta": -c_plus["C_phi_phi_over_sin2theta"],
        "screen_trace_qAB_C_AB": -c_plus["screen_trace_qAB_C_AB"],
    }
    jump = {
        key: c_plus[key] - c_minus[key]
        for key in [
            "C_TT",
            "C_theta_theta_over_unit_sphere",
            "C_phi_phi_over_sin2theta",
            "screen_trace_qAB_C_AB",
        ]
    }
    stress = {
        "mu_proportional_to_minus_screen_jump": -jump["screen_trace_qAB_C_AB"],
        "p_proportional_to_minus_generator_jump": -jump["C_TT"],
        "jA": 0.0,
    }
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "route": "PT_orientation_reversing_null_transverse_curvature_pullback",
        "regular_hK_pipeline_allowed": False,
        "uses_free_orientation_sign": False,
        "PT_bridge_null_geometry_used": True,
        "explicit_minus_metric_components_available": False,
        "PT_pullback_sign_rule": "C_minus_ab = - C_plus_ab",
        "sign_rule_source": (
            "orientation-reversing PT bridge pullback of the null transverse "
            "normal in the active Eddington/PT branch"
        ),
        "C_plus": c_plus,
        "C_minus_from_PT_pullback": c_minus,
        "jump_from_PT_pullback": jump,
        "stress_from_PT_pullback": stress,
        "PT_pullback_transverse_curvature_ready": True,
        "active_stress_mapping_ready": True,
        "absolute_Rs_selected": False,
        "scale_selection_ready": False,
        "next_required": [
            "derive_or_supply_absolute_Rs_or_mass_charge",
            "derive_null_Bianchi_balance_with_stress_slots",
        ],
    }
