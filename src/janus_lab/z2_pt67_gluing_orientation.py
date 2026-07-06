"""PT gluing orientation for the chapter 6.7 regular surface."""

from __future__ import annotations

from src.janus_lab.z2_pt67_regular_surface import pt67_regular_surface_geometry


def pt67_gluing_orientation_payload(rs: float = 1.0) -> dict:
    surface = pt67_regular_surface_geometry(rs)
    k = surface["extrinsic_curvature_local"]

    return {
        "active_core": "Z2_tunnel_Sigma",
        "route": "chapter_6_7_regular_PT_transfer_cross_term_surface",
        "input_regular_surface_ready": surface["regularity_at_sigma"]["regular_hK_pipeline_allowed"],
        "PT_transport_rule": {
            "time_covector": "dt -> -dt",
            "radial_covector": "dr -> dr",
            "screen_metric": "gamma_AB transported by the projective angular identification",
            "normal_covector": "n=dr/sqrt(2) is PT-invariant",
        },
        "extrinsic_curvature_transport": {
            "K_TT_first": k["K_TT"],
            "K_TT_second_PT_pullback": k["K_TT"],
            "K_AB_first": k["K_thetatheta"],
            "K_AB_second_PT_pullback": k["K_thetatheta"],
            "reason": "K_TT has two time tangents, so the PT time sign squares to +1; angular block is screen-transported.",
        },
        "DeltaK_PT_transport": {
            "DeltaK_TT": 0.0,
            "DeltaK_thetatheta": 0.0,
            "DeltaK_phiphi": "0",
            "DeltaK_screen_trace": 0.0,
            "DeltaK_ready": True,
        },
        "not_using": {
            "outward_Israel_cut_and_paste_normals": True,
            "free_orientation_sign": True,
            "fit_parameter": True,
        },
        "raccord_to_regular_sigma_pipeline": {
            "h_ab_ready": True,
            "unit_normal_ready": True,
            "K_ab_local_ready": True,
            "DeltaK_PT_transport_ready": True,
            "Cartan_GHY_jump_ready_under_PT_transport": True,
        },
    }
