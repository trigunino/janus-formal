"""Null-generator normalization for the Janus PT bridge."""

from __future__ import annotations

from src.janus_lab.z2_null_sigma_pt_joint import null_sigma_pt_joint_payload


def null_sigma_generator_normalization_payload(rs: float = 1.0) -> dict:
    if rs <= 0.0:
        raise ValueError("rs must be positive")

    joint = null_sigma_pt_joint_payload(rs)
    inner = joint["PT_joint_model"]["canonical_inner_product_lplus_nminus"]
    fixed = inner == -1.0 and joint["normalization_policy"][
        "canonical_PT_normalization_fixed"
    ]
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "route": "canonical_PT_null_generator_normalization",
        "regular_hK_pipeline_allowed": False,
        "normalization_condition": "l_plus dot n_minus = -1",
        "canonical_inner_product_lplus_nminus": inner,
        "free_boost_rescaling_allowed": False,
        "boost_parameter_alpha_fixed": 1.0 if fixed else None,
        "general_boost_rescaling_quotient_needed": False,
        "null_generator_rescaling_quotiented": fixed,
        "reason": (
            "The PT bridge fixes the relative null-generator scaling by the "
            "canonical cross-normalization used in the joint term. A free boost "
            "would change the joint normalization and is not an active symmetry "
            "of this fixed-boundary branch."
        ),
    }
