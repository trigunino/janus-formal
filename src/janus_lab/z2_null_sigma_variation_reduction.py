"""Symbolic reduction of the null-boundary density variation."""

from __future__ import annotations

from src.janus_lab.z2_null_sigma_action_variation import (
    null_sigma_action_variation_payload,
)


def null_sigma_variation_reduction_payload(rs: float = 1.0) -> dict:
    if rs <= 0.0:
        raise ValueError("rs must be positive")

    action = null_sigma_action_variation_payload(rs)
    sqrt_q = action["null_boundary_density"]["sqrt_q_over_sin_theta"]
    kappa = action["null_boundary_density"]["kappa_l"]

    delta_sqrt_q_coeff = 2.0 * rs
    delta_kappa_coeff = -1.0 / (2.0 * rs * rs)
    radial_density_coeff = kappa * delta_sqrt_q_coeff + sqrt_q * delta_kappa_coeff

    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "input_action_density_ready": action["input_variables_ready"],
        "regular_hK_pipeline_allowed": False,
        "null_density": action["null_boundary_density"],
        "variation_formulae": {
            "delta_density_symbolic": "delta(sqrt(q) kappa_l) = kappa_l delta(sqrt(q)) + sqrt(q) delta(kappa_l)",
            "delta_sqrt_q_symbolic": "delta(sqrt(q)) = 1/2 sqrt(q) q^AB delta(q_AB)",
            "so3_radial_delta_sqrt_q_over_sin_theta": "2 R_s deltaR_s",
            "so3_radial_delta_kappa_l": "-deltaR_s/(2 R_s^2)",
        },
        "radial_reduction": {
            "R_s": rs,
            "delta_sqrt_q_coefficient_over_sin_theta": delta_sqrt_q_coeff,
            "delta_kappa_coefficient": delta_kappa_coeff,
            "delta_density_coefficient_over_sin_theta": radial_density_coeff,
            "delta_density_over_sin_theta": f"{radial_density_coeff} * deltaR_s",
        },
        "bulk_null_density_variation_reduced": True,
        "PT_joint_term_ready": False,
        "null_generator_rescaling_quotiented": False,
        "null_shell_stress_mapping_ready": False,
        "null_junction_balance_ready": False,
        "reason_not_junction_ready": (
            "The bulk null density variation is reduced, but the PT joint term, "
            "generator-rescaling policy and Barrabes-Israel stress mapping are still open."
        ),
        "next_required": [
            "derive PT joint/corner variation across the two sheets",
            "fix or quotient the null-generator rescaling ambiguity",
            "map reduced variation slots to Barrabes-Israel null shell stress data",
        ],
    }
