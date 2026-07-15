from __future__ import annotations

from scripts.audit_janus_worldvolume_mcs_one_loop_scheme import build_audit


def test_cutoff_scheme_requires_quartic_counterterm() -> None:
    audit = build_audit()
    assert audit.quartic_counterterm_required_in_cutoff_scheme
    assert audit.induced_scalar_shapes["Lambda_m2"] == "Lambda*kappa^2*phi^4"
    assert "Lambda*m**2" in audit.divergent_potential_term


def test_one_loop_finite_piece_is_sextic_but_not_a_beta_claim() -> None:
    audit = build_audit()
    assert audit.induced_scalar_shapes["m3"] == "abs(kappa)^3*phi^6"
    assert not audit.logarithmic_divergence_found_at_this_order
    assert audit.mcs_one_loop_ms_sextic_beta_contribution == 0
    assert not audit.sextic_finite_part_scheme_independent
    assert audit.verdict == "power_subtractions_and_finite_sextic_condition_required"
