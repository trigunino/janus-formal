"""Chapter 6.7 PT-transfer regular surface geometry."""

from __future__ import annotations

from math import sqrt


def pt67_metric_block(r: float, rs: float = 1.0, sheet_epsilon: int = 1) -> dict:
    if r <= 0.0 or rs <= 0.0:
        raise ValueError("r and rs must be positive")
    if sheet_epsilon not in (-1, 1):
        raise ValueError("sheet_epsilon must be -1 or +1")

    x = rs / r
    a_tt = 1.0 + x
    b_rr_symbol = 1.0 - x
    c_tr = float(sheet_epsilon) * x
    det_tr = -a_tt * b_rr_symbol - c_tr * c_tr
    g_rr_inverse = a_tt / det_tr
    return {
        "r_over_rs": r / rs,
        "sheet_epsilon": sheet_epsilon,
        "A_TT": a_tt,
        "B_RR_positive_symbol": b_rr_symbol,
        "C_TR": c_tr,
        "det_TR_block": det_tr,
        "g_inverse_rr": g_rr_inverse,
        "induced_time_component_on_r_const": a_tt,
    }


def pt67_regular_surface_geometry(rs: float = 1.0) -> dict:
    if rs <= 0.0:
        raise ValueError("rs must be positive")

    plus = pt67_metric_block(rs, rs, sheet_epsilon=-1)
    minus = pt67_metric_block(rs, rs, sheet_epsilon=1)
    normal_covector_scale = 1.0 / sqrt(2.0)
    k_tt = 1.0 / (sqrt(2.0) * rs)
    k_sphere = sqrt(2.0) * rs
    k_screen_trace = 2.0 * sqrt(2.0) / rs

    return {
        "active_core": "Z2_tunnel_Sigma",
        "route": "chapter_6_7_regular_PT_transfer_cross_term_surface",
        "source_anchor": "The_Janus_Cosmological_Model chapter 6.7, equations 6.7.2-6.7.4",
        "metric_convention": "ds^2=A dt^2 + 2C dt dr - B dr^2 - r^2 dOmega^2",
        "formula": {
            "A": "1 + R_s/r",
            "B": "1 - R_s/r",
            "C_plus_first_sheet": "-R_s/r",
            "C_minus_second_sheet": "+R_s/r",
        },
        "sheets_at_sigma": {
            "first_sheet": plus,
            "second_sheet": minus,
        },
        "regularity_at_sigma": {
            "r_sigma": rs,
            "det_TR_block": -1.0,
            "induced_h_TT": 2.0,
            "induced_h_thetatheta": -(rs * rs),
            "induced_h_phiphi": "-R_s^2 sin(theta)^2",
            "induced_surface_degenerate": False,
            "regular_hK_pipeline_allowed": True,
        },
        "unit_normal": {
            "covector_basis": "[dt, dr, dtheta, dphi]",
            "n_covector": [0.0, normal_covector_scale, 0.0, 0.0],
            "normal_norm": -1.0,
            "orientation": "one-sided local normal; gluing jump orientation not yet fixed",
        },
        "extrinsic_curvature_local": {
            "definition": "K_ab = - n_mu Gamma^mu_ab on r=R_s",
            "K_TT": k_tt,
            "K_thetatheta": k_sphere,
            "K_phiphi": f"{k_sphere} * sin(theta)^2",
            "screen_trace_qAB_K_AB": k_screen_trace,
        },
        "raccord_to_regular_sigma_pipeline": {
            "h_ab_ready": True,
            "unit_normal_ready": True,
            "K_ab_local_ready": True,
            "DeltaK_plus_minus_ready": False,
            "reason_deltaK_not_ready": "The inter-sheet jump still needs the active Z2 gluing orientation convention, not a free sign choice.",
        },
    }
