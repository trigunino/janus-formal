"""PT joint term reduction for the null Sigma bridge."""

from __future__ import annotations

from src.janus_lab.z2_null_sigma_variation_reduction import (
    null_sigma_variation_reduction_payload,
)


def null_sigma_pt_joint_payload(rs: float = 1.0) -> dict:
    variation = null_sigma_variation_reduction_payload(rs)
    canonical_inner_product = -1.0
    joint_log_argument = abs(canonical_inner_product)
    joint_density = 0.0

    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "input_bulk_variation_reduced": variation["bulk_null_density_variation_reduced"],
        "regular_hK_pipeline_allowed": False,
        "PT_joint_model": {
            "symbolic": "sqrt(q) log(|-l_+ . n_-|)",
            "canonical_inner_product_lplus_nminus": canonical_inner_product,
            "log_argument": joint_log_argument,
            "joint_density_over_sin_theta": joint_density,
            "delta_joint_density_over_sin_theta": 0.0,
        },
        "normalization_policy": {
            "canonical_PT_normalization_fixed": True,
            "normalization_condition": "l_+ . n_- = -1",
            "free_boost_rescaling_allowed": False,
            "general_rescaling_quotient_proved": False,
        },
        "PT_joint_term_reduced": True,
        "PT_joint_term_ready": True,
        "bulk_null_density_variation_reduced": True,
        "null_shell_stress_mapping_ready": False,
        "null_junction_balance_ready": False,
        "reason_not_junction_ready": (
            "The canonical PT joint contributes zero, but the reduced bulk "
            "variation is not yet mapped to Barrabes-Israel null-shell stress data."
        ),
        "next_required": [
            "map reduced bulk variation to Barrabes-Israel null shell stress data",
            "derive null Bianchi balance across the PT bridge",
        ],
    }
