from scripts.derive_bimetric_cosmological_higuchi_gate import build_payload


def test_higuchi_and_strong_coupling_conditions_are_explicit():
    payload = build_payload()
    conditions = payload["conditions"]
    assert conditions["helicity0_no_ghost"] == "Delta_bi>0"
    assert conditions["strong_coupling_surface"] == "Delta_bi=0"
    assert "H_plus(t),H_minus(t)" in conditions["trajectory_condition"]
    assert "beta1" in payload["dressed_polynomial"]


def test_background_dependence_is_not_hidden():
    closure = build_payload()["closure"]
    assert closure["full_two_hubble_higuchi_gate"]
    assert closure["strong_coupling_surface_identified"]
    assert not closure["full_time_dependent_background_supplied"]
    assert not closure["trajectory_stability_decided"]
