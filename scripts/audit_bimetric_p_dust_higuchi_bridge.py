from __future__ import annotations

from fractions import Fraction


def hubble_from_phase_point(momentum, planck_sq, scale_factor):
    return -momentum / (6 * planck_sq * scale_factor**2)


def symmetric_dust_higuchi_gap(mass_sq):
    h = Fraction(1, 6)
    return 2 * h**4 * (mass_sq - h**2)


def two_hubble_gap(h_plus, h_minus, mass_sq):
    return mass_sq * (h_plus**2 + h_minus**2) ** 2 / 2 - 2 * h_plus**3 * h_minus**3


def stable_box_certificate(center, radius, mass_sq):
    if min(center, radius, mass_sq) < 0:
        raise ValueError("center, radius and mass_sq must be nonnegative")
    upper = center + radius
    certified = upper**2 < mass_sq and radius < center
    return {"upper_hubble": upper, "max_product_bound": upper**2,
            "strictly_positive_hubbles": radius < center,
            "higuchi_certified": certified}


def build_payload() -> dict:
    h = hubble_from_phase_point(Fraction(1), Fraction(1), Fraction(1))
    gap_at_unit_mass = symmetric_dust_higuchi_gap(Fraction(1))
    return {
        "artifact": "bimetric_p_dust_higuchi_bridge",
        "p_witness": "a_plus=a_minus=p_plus=p_minus=M_plus^2=M_minus^2=1",
        "hamilton_equation": "H=-p/(6 M^2 a^2)",
        "hubble": str(h),
        "beta_branch": "beta1=beta3=1, beta2=0",
        "gap": "Delta_bi=2 H^4 (m^2-H^2)",
        "healthy_condition": "m^2>1/36",
        "two_hubble_sufficient_condition": "H_plus>0, H_minus>0 and H_plus*H_minus<m^2",
        "unit_mass_symmetric_box": "|H_plus-1/6|<epsilon and |H_minus-1/6|<epsilon is certified for 0<=epsilon<1/6",
        "unit_mass_gap": str(gap_at_unit_mass),
        "closure": {
            "instantaneous_p_witness_higuchi_condition_derived": True,
            "unit_mass_witness_strictly_healthy": gap_at_unit_mass > 0,
            "positive_neighborhood_certificate_derived": True,
            "p_interaction_scale_equals_b_canonical_mass_proved": False,
            "time_dependent_trajectory_stability_proved": False,
        },
    }
