"""Signed Schwarzschild SO(3) metric blocks for Janus reduced sectors."""

from __future__ import annotations


def signed_schwarzschild_f(R: float, Rs: float = 1.0, interaction_sign: int = 1) -> float:
    """Return f(R)=1-sign*Rs/R.

    interaction_sign=+1 is same-sign attraction; -1 is opposite-sign repulsion.
    """

    if R <= 0.0 or Rs <= 0.0:
        raise ValueError("R and Rs must be positive")
    if interaction_sign not in (-1, 1):
        raise ValueError("interaction_sign must be +1 or -1")
    return 1.0 - float(interaction_sign) * float(Rs) / float(R)


def signed_schwarzschild_df_dR(R: float, Rs: float = 1.0, interaction_sign: int = 1) -> float:
    if R <= 0.0 or Rs <= 0.0:
        raise ValueError("R and Rs must be positive")
    if interaction_sign not in (-1, 1):
        raise ValueError("interaction_sign must be +1 or -1")
    return float(interaction_sign) * float(Rs) / (float(R) * float(R))


def signed_schwarzschild_metric_diagnostic(rs: float = 1.0) -> dict:
    radii = [rs, 1.25 * rs, 2.0 * rs]
    samples = [
        {
            "R_over_Rs": R / rs,
            "f_attractive": signed_schwarzschild_f(R, rs, +1),
            "df_attractive_dR": signed_schwarzschild_df_dR(R, rs, +1),
            "f_repulsive": signed_schwarzschild_f(R, rs, -1),
            "df_repulsive_dR": signed_schwarzschild_df_dR(R, rs, -1),
        }
        for R in radii
    ]
    return {
        "active_core": "Z2_tunnel_Sigma",
        "metric_family": "signed_schwarzschild_exterior_blocks",
        "formula": "f_epsilon(R)=1-epsilon*R_s/R",
        "epsilon_policy": {
            "+1": "same-sign attractive Schwarzschild block",
            "-1": "opposite-sign repulsive Janus block",
        },
        "samples": samples,
        "attractive_block_degenerate_at_Rs": signed_schwarzschild_f(rs, rs, +1) == 0.0,
        "repulsive_block_regular_at_Rs": signed_schwarzschild_f(rs, rs, -1) > 0.0,
        "thin_shell_K_formula_ready_at_Rs": False,
        "reason_not_ready_at_Rs": "attractive f(R_s)=0 makes the static exterior-coordinate shell radicand degenerate",
        "allowed_use": [
            "metric-function diagnostic away from the throat",
            "input to dynamic shell formulas only where Rdot^2+f>0",
        ],
        "next_required": [
            "derive a regular throat collar/Kruskal-like chart at R=R_s",
            "or restrict thin-shell DeltaK tests to R>R_s as diagnostic-only",
            "do not use exterior-coordinate f(R_s)=0 as active DeltaK closure",
        ],
    }
