"""Eddington-style cross-term SO(3) collar diagnostic."""

from __future__ import annotations


def eddington_cross_term_block(R: float, Rs: float = 1.0) -> dict:
    """Return the dimensionless (T,R) block from the document's cross-term route.

    Convention:
      ds^2 = A dT^2 + 2 C dT dR - B dR^2 - R^2 dOmega^2
      A = 1 - Rs/R, B = 1 + Rs/R, C = -Rs/R.

    Then det[[A,C],[C,-B]] = -1, including at R=Rs.
    """

    if R <= 0.0 or Rs <= 0.0:
        raise ValueError("R and Rs must be positive")
    x = float(Rs) / float(R)
    a = 1.0 - x
    b = 1.0 + x
    c = -x
    return {
        "R_over_Rs": float(R) / float(Rs),
        "A_TT": a,
        "B_RR_positive_symbol": b,
        "C_TR": c,
        "det_TR_block": -a * b - c * c,
        "induced_time_component_on_R_const": a,
    }


def eddington_cross_term_collar_diagnostic(rs: float = 1.0) -> dict:
    throat = eddington_cross_term_block(rs, rs)
    outside = eddington_cross_term_block(1.25 * rs, rs)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "Janus reference chapter 6 cross-term drdt route",
        "reference_pages": {
            "cross_term_motivation": "177-181",
            "finite_infall_metric": "181",
            "PT_bridge_interpretation": "182-183",
        },
        "metric_block_convention": "ds^2=A dT^2 + 2C dT dR - B dR^2 - R^2 dOmega^2",
        "formula": {
            "A": "1 - R_s/R",
            "B": "1 + R_s/R",
            "C": "-R_s/R",
            "det_TR": "-1",
        },
        "samples": [throat, outside],
        "bulk_TR_block_regular_at_Rs": throat["det_TR_block"] == -1.0,
        "R_const_throat_induced_metric_null": throat["induced_time_component_on_R_const"] == 0.0,
        "even_radius_fold_coordinate_degenerates_at_sigma": True,
        "current_regular_sigma_hK_formalism_compatible": False,
        "interpretation": (
            "The drdt cross term fixes the exterior-coordinate bulk degeneracy, "
            "but the R=R_s throat is null for the induced metric. Pulling it back "
            "through an even fold coordinate R(rho) with R'(0)=0 degenerates the "
            "(T,rho) block. This is a null/junction branch, not the current regular "
            "Sigma h_ab,K_ab branch."
        ),
        "route_decision": {
            "regular_timelike_sigma": "requires a non-horizon throat with A(0) != 0 or an independent regular collar not equal to exterior Schwarzschild",
            "null_sigma_bridge": "requires null-shell / horizon boundary formalism instead of the current GHY h,K pipeline",
        },
        "next_required": [
            "choose null Sigma formalism if the Eddington/PT bridge is active",
            "or derive a different regular non-horizon collar from the bimetric action",
            "do not feed the Eddington R=R_s throat into regular h_ab,K_ab counterterm gates",
        ],
    }
