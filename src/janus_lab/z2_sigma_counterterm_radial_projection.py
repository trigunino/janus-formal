"""Symbolic radial projection of the active Z2/Sigma counterterm primitive."""

from __future__ import annotations


def build_counterterm_radial_projection_formula(
    *,
    dimension: int,
    torsion_coefficient_ready: bool,
) -> dict:
    if dimension <= 0:
        raise ValueError("dimension must be positive")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "projection_kind": "symbolic_radial_projection_of_field_space_primitive",
        "dimension": int(dimension),
        "primitive": "L_ct = - integral_gamma alpha_res",
        "radial_derivative": (
            "partial_R L_ct = -(R_h^{ab} partial_R h_ab + "
            "R_K^{ab} partial_R K_ab + R_T^A partial_R T_A + "
            "R_chi partial_R chi)"
        ),
        "active_collar_substitution": {
            "partial_R_h_ab": "2 R_Sigma q_ab",
            "partial_R_K_ab": "q_ab",
            "partial_R_T_A": "0 on active torsionless Sigma branch"
            if torsion_coefficient_ready
            else "requires active torsion variation",
        },
        "reduced_radial_derivative": (
            "partial_R L_ct = -(2 R_Sigma R_h^{ab} q_ab + "
            "R_K^{ab} q_ab + R_chi partial_R chi)"
            if torsion_coefficient_ready
            else "partial_R L_ct still includes R_T^A partial_R T_A"
        ),
        "E_counterterm_formula": (
            "E_counterterm = partial_R(sqrt|h| L_ct) = "
            "(partial_R sqrt|h|) L_ct + sqrt|h| partial_R L_ct"
        ),
        "sqrt_h_substitution": {
            "sqrt_abs_h": f"R_Sigma^{dimension} sqrt(det q)",
            "partial_R_sqrt_abs_h": f"{dimension} R_Sigma^{dimension - 1} sqrt(det q)",
        },
        "value_profile_ready": False,
        "still_requires_for_values": ["R_h^{ab} q_ab", "R_K^{ab} q_ab", "R_chi partial_R chi", "L_ct integration constant/profile"],
    }
