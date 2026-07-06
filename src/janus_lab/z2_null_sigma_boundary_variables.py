"""Null boundary variables for the Janus PT bridge at R=R_s."""

from __future__ import annotations


def null_sigma_boundary_variables_payload(rs: float = 1.0) -> dict:
    if rs <= 0.0:
        raise ValueError("rs must be positive")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "coordinate_basis": ["T", "R", "theta", "phi"],
        "Sigma": "R=R_s",
        "metric_block_at_Sigma": {
            "g_TT": 0.0,
            "g_TR": -1.0,
            "g_RR": -2.0,
            "det_TR": -1.0,
        },
        "null_generator_l_vector": [1.0, 0.0, 0.0, 0.0],
        "auxiliary_null_n_vector": [-1.0, 1.0, 0.0, 0.0],
        "normalization": {
            "l_dot_l": 0.0,
            "n_dot_n": 0.0,
            "l_dot_n": -1.0,
        },
        "screen_metric_q_AB": {
            "q_thetatheta": rs * rs,
            "q_phiphi": "R_s^2 sin(theta)^2",
        },
        "SO3_null_kinematics": {
            "theta_l_expansion": 0.0,
            "shear_l_AB": 0.0,
            "twist_l": 0.0,
            "inaffinity_kappa_l": 1.0 / (2.0 * rs),
        },
        "PT_bridge_transport": {
            "time_reversal_at_crossing": True,
            "orientation_reversal_at_crossing": True,
            "mass_energy_inversion_slot": "Souriau_PT",
            "one_way_membrane_slot": True,
        },
        "null_boundary_variables_declared": True,
        "null_action_variation_ready": False,
        "null_junction_balance_ready": False,
        "regular_hK_pipeline_allowed": False,
        "next_required": [
            "derive null boundary action variation with q_AB, theta, kappa",
            "derive null junction/Bianchi balance across the PT bridge",
            "transport Souriau PT mass-energy inversion into the null shell balance",
        ],
    }
