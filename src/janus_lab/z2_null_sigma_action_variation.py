"""Null-boundary action variation target for the Janus PT bridge."""

from __future__ import annotations

from src.janus_lab.z2_null_sigma_boundary_variables import (
    null_sigma_boundary_variables_payload,
)


def null_sigma_action_variation_payload(rs: float = 1.0) -> dict:
    variables = null_sigma_boundary_variables_payload(rs)
    sqrt_q = rs * rs
    kappa = variables["SO3_null_kinematics"]["inaffinity_kappa_l"]
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "bibliography": {
            "null_gr_action": "Lehner-Myers-Poisson-Sorkin, arXiv:1609.00207",
            "null_counterterm": "Parattu-Chakraborty-Majhi-Padmanabhan, arXiv:1501.01053",
            "null_shell_junction": "Barrabes-Israel / Poisson reformulation, arXiv:gr-qc/0207101",
        },
        "input_variables_ready": variables["null_boundary_variables_declared"],
        "regular_hK_pipeline_allowed": False,
        "null_boundary_density": {
            "symbolic": "sqrt(q) * kappa_l",
            "sqrt_q_over_sin_theta": sqrt_q,
            "kappa_l": kappa,
            "density_over_sin_theta": sqrt_q * kappa,
        },
        "parametrization_policy": {
            "generator_parametrization_fixed": True,
            "affine_parametrization": False,
            "reason": "Eddington horizon generator has nonzero inaffinity kappa_l=1/(2R_s)",
            "rescaling_ambiguity_recorded": True,
        },
        "variation_slots_declared": {
            "delta_q_AB": True,
            "delta_kappa_l": True,
            "delta_l_rescaling": True,
            "corner_joint_variation": True,
        },
        "null_action_variation_ready": False,
        "reason_not_ready": (
            "The density sqrt(q) kappa_l is identified, but its Janus/PT variation "
            "and joint/corner contribution across the two sheets are not derived."
        ),
        "null_junction_balance_ready": False,
        "next_required": [
            "derive delta(sqrt(q) kappa_l) under allowed PT/Z2 variations",
            "fix or quotient the null generator rescaling ambiguity",
            "derive the corner/joint term at the PT sheet crossing",
            "map the resulting variation to a Barrabes-Israel null shell stress slot",
        ],
    }
