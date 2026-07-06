"""Endpoint verdict for the null Sigma/PT bridge attempt."""

from __future__ import annotations

from src.janus_lab.z2_null_sigma_barrabes_israel import (
    null_sigma_barrabes_israel_payload,
)


def null_sigma_branch_verdict_payload() -> dict:
    bi = null_sigma_barrabes_israel_payload()

    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "null_branch_inputs_reduced": {
            "boundary_variables": True,
            "bulk_density_variation": True,
            "canonical_PT_joint": True,
            "plus_side_transverse_curvature": True,
            "transverse_curvature_jump": bi["jump_policy"]["jump_C_ab_derived"],
        },
        "null_branch_closure": {
            "null_shell_stress_mapping_ready": False,
            "null_junction_balance_ready": False,
            "reason": "Barrabes-Israel stress needs the derived inter-sheet transverse-curvature jump [C_ab].",
        },
        "source_consistency_frontier": {
            "chapter_6_3_eddington_surface": "null/degenerate horizon reading",
            "chapter_6_7_PT_transfer_surface": "sign-flipped integration constant gives regular cross-term transfer metric",
            "chapter_6_7_metric_at_r_equals_a": {
                "g_tt": 2.0,
                "g_tr_signs": ["first_sheet=-1", "second_sheet=+1"],
                "g_rr": 0.0,
                "det_tr_block": -1.0,
                "induced_surface_degenerate": False,
            },
        },
        "verdict": {
            "null_branch_exhausted_without_sparadrap": True,
            "promote_null_shell_model": False,
            "recommended_next_active_route": "chapter_6_7_regular_PT_transfer_cross_term_surface",
            "regular_hK_reopen_allowed_on_6_7_route": True,
        },
        "next_required": [
            "build the 6.7 PT transfer metric as the active collar",
            "derive h_ab and K_ab at r=a with g_tt=2 and det(T,r)=-1",
            "feed that nondegenerate surface back into the regular Sigma h/K pipeline",
        ],
    }
