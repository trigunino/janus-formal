from scripts.audit_gw_observational_bounds import (
    GWTC3_GRAVITON_MASS_EV,
    audit_candidate,
)


def test_gr_limit_passes_generic_bounds():
    payload = audit_candidate(0.0, 0.0)
    assert payload["passes_mass_bound"]
    assert payload["passes_speed_bound"]
    assert not payload["fit_used"]


def test_out_of_range_candidate_is_rejected():
    payload = audit_candidate(2.0 * GWTC3_GRAVITON_MASS_EV, 1.0e-10)
    assert not payload["passes_mass_bound"]
    assert not payload["passes_speed_bound"]
