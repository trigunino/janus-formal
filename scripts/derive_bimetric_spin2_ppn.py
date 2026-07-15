from __future__ import annotations

import json
import os
from pathlib import Path

import sympy as sp


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
ALPHA, Y, MASS, RADIUS, SCHWARZSCHILD_RADIUS = sp.symbols(
    "alpha y m r r_s", positive=True
)
CASSINI_SIGMA = sp.Rational(23, 10**6)
C, S = sp.symbols("c s", positive=True)


def phi_factor(alpha: sp.Expr = ALPHA, y: sp.Expr = Y) -> sp.Expr:
    return 1 + sp.Rational(4, 3) * alpha * y


def psi_factor(alpha: sp.Expr = ALPHA, y: sp.Expr = Y) -> sp.Expr:
    return 1 + sp.Rational(2, 3) * alpha * y


def gamma_ppn(alpha: sp.Expr = ALPHA, y: sp.Expr = Y) -> sp.Expr:
    return sp.factor(psi_factor(alpha, y) / phi_factor(alpha, y))


def vainshtein_screening() -> sp.Expr:
    """Positive branch of u+c*u^2=s, normalized by the linear solution u=s."""
    return sp.factor(2 / (1 + sp.sqrt(1 + 4 * C * S)))


def channel(alpha: sp.Expr) -> dict:
    return {
        "alpha": str(alpha),
        "Phi_over_Phi_GR": str(phi_factor(alpha)),
        "Psi_over_Psi_GR": str(psi_factor(alpha)),
        "gamma": str(gamma_ppn(alpha)),
        "short_distance_gamma": str(sp.factor(gamma_ppn(alpha, 1))),
    }


def build_payload() -> dict:
    k_plus, k_minus = sp.symbols("K_plus K_minus", positive=True)
    cassini_positive_alpha_y_max = sp.factor(
        3 * CASSINI_SIGMA / (2 - 4 * CASSINI_SIGMA)
    )
    cross_short_phi = sp.factor(phi_factor(-1, 1))
    cross_short_psi = sp.factor(psi_factor(-1, 1))
    return {
        "artifact": "bimetric_spin2_ppn",
        "status": "linear_spin2_projectors_and_ppn_yukawa_derived",
        "fit_used": False,
        "projectors_for_conserved_sources": {
            "massless": "Tmunu*Tmunu-(1/2)*T*T",
            "massive_fierz_pauli": "Tmunu*Tmunu-(1/3)*T*T",
            "newtonian_massive_enhancement": "4/3",
            "spatial_curvature_massive_enhancement": "2/3",
        },
        "general": {
            "y": "exp(-m*r)",
            "G_eff_over_G0": str(phi_factor()),
            "gamma": str(gamma_ppn()),
            "gamma_minus_one": str(sp.factor(gamma_ppn() - 1)),
        },
        "channels": {
            "plus_plus": channel(k_minus / k_plus),
            "minus_minus": channel(k_plus / k_minus),
            "cross": channel(sp.Integer(-1)),
        },
        "cross_short_distance": {
            "Phi_factor": str(cross_short_phi),
            "Psi_factor": str(cross_short_psi),
            "scalar_kernel_cancellation_survives_spin2": cross_short_phi == 0 and cross_short_psi == 0,
        },
        "vdvz": {
            "pure_massive_gamma": "1/2",
            "equal_kinetic_unsuppressed_gamma": str(gamma_ppn(1, 1)),
            "linear_GR_limit_as_m_to_zero": False,
        },
        "cassini": {
            "measurement": "gamma-1=(2.1+/-2.3)*10^-5",
            "one_sigma_abs_scale": str(CASSINI_SIGMA),
            "positive_alpha_times_exp_bound_at_one_sigma": str(cassini_positive_alpha_y_max),
        },
        "vainshtein": {
            "radius": "r_V=(r_s/m^2)^(1/3)",
            "condition_for_solar_system_GR": "measurement radius << r_V",
            "reduced_helicity0_equation": "u+c*u^2=(r_V/r)^3",
            "screening_factor": str(vainshtein_screening()),
            "deep_screening_scaling": "screening ~ (r/r_V)^(3/2)/sqrt(c)",
            "healthy_reduced_branch_condition": "c>0",
            "nonlinear_solution_derived_here": True,
            "full_candidate_beta_to_c_map_derived": False,
        },
        "closure": {
            "full_conserved_source_spin2_projectors": True,
            "linear_ppn_gamma": True,
            "channel_matrix": True,
            "cassini_diagnostic": True,
            "reduced_vainshtein_profile": True,
            "full_candidate_vainshtein_profile": False,
            "preferred_frame_ppn": False,
        },
    }


def write_report() -> dict:
    payload = build_payload()
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    (REPORT_DIR / "bimetric_spin2_ppn.json").write_text(
        json.dumps(payload, indent=2), encoding="utf-8"
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_report(), indent=2))
