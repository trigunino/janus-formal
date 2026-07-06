"""Barrabes-Israel data slots for the Janus null Sigma bridge."""

from __future__ import annotations

from src.janus_lab.z2_null_sigma_pt_joint import null_sigma_pt_joint_payload


def null_sigma_barrabes_israel_payload(rs: float = 1.0) -> dict:
    if rs <= 0.0:
        raise ValueError("rs must be positive")

    joint = null_sigma_pt_joint_payload(rs)
    c_tt = 1.0 / (2.0 * rs)
    c_theta_theta_over_unit_sphere = -rs
    c_screen_trace = -2.0 / rs

    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "input_PT_joint_ready": joint["PT_joint_term_ready"],
        "regular_hK_pipeline_allowed": False,
        "barrabes_israel_reference": "Barrabes-Israel null shell stress uses transverse curvature jump [C_ab]",
        "transverse_curvature_plus_side": {
            "definition": "C_ab = -N_mu e_a^nu nabla_nu e_b^mu",
            "C_TT": c_tt,
            "C_theta_theta_over_unit_sphere": c_theta_theta_over_unit_sphere,
            "C_phi_phi_over_sin2theta": c_theta_theta_over_unit_sphere,
            "screen_trace_qAB_C_AB": c_screen_trace,
        },
        "jump_policy": {
            "PT_orientation_reversal_declared": True,
            "requires_minus_side_transverse_curvature": True,
            "minus_side_curvature_derived": False,
            "jump_C_ab_derived": False,
            "reason": "PT orientation/time reversal is declared, but the actual minus-side transverse curvature pullback is not yet derived from the second sheet metric.",
        },
        "stress_slots": {
            "surface_energy_mu_from_screen_jump": "mu ~ - q^AB [C_AB]",
            "surface_current_jA_from_mixed_jump": "j_A ~ [C_TA]",
            "surface_pressure_p_from_generator_jump": "p ~ - [C_TT]",
            "all_values_blocked_until_jump_C_ab": True,
        },
        "bulk_variation_radial_coefficient_over_sin_theta": 0.5,
        "null_shell_stress_mapping_ready": False,
        "null_junction_balance_ready": False,
        "next_required": [
            "derive minus-side transverse curvature C_ab^- from the PT transported metric",
            "derive [C_ab] without choosing a free orientation sign",
            "then compute mu, j_A and p from the Barrabes-Israel formulas",
        ],
    }
