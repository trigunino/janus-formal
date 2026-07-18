from fractions import Fraction

from scripts.audit_bimetric_p_dust_higuchi_bridge import (
    build_payload,
    hubble_from_phase_point,
    symmetric_dust_higuchi_gap,
    stable_box_certificate,
    two_hubble_gap,
)


def test_p_dust_witness_hubble_is_exact():
    assert hubble_from_phase_point(Fraction(1), Fraction(1), Fraction(1)) == Fraction(-1, 6)


def test_higuchi_threshold_and_unit_mass_gap():
    assert symmetric_dust_higuchi_gap(Fraction(1, 36)) == 0
    assert symmetric_dust_higuchi_gap(Fraction(1)) == Fraction(35, 23328)
    assert build_payload()["closure"]["unit_mass_witness_strictly_healthy"]


def test_bridge_limit_is_explicit():
    closure = build_payload()["closure"]
    assert not closure["p_interaction_scale_equals_b_canonical_mass_proved"]
    assert not closure["time_dependent_trajectory_stability_proved"]


def test_positive_hubble_product_condition_is_sufficient():
    hp, hm, mass_sq = Fraction(1, 4), Fraction(1, 5), Fraction(1, 10)
    assert hp * hm < mass_sq
    assert two_hubble_gap(hp, hm, mass_sq) > 0


def test_unit_mass_box_around_witness_is_certified():
    certificate = stable_box_certificate(Fraction(1, 6), Fraction(1, 12), Fraction(1))
    assert certificate["higuchi_certified"]
    assert certificate["max_product_bound"] == Fraction(1, 16)
