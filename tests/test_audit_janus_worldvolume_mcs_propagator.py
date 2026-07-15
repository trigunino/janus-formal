from __future__ import annotations

from scripts.audit_janus_worldvolume_mcs_propagator import build_audit


def test_transverse_mcs_propagator_inverts_kinetic_block() -> None:
    audit = build_audit()
    assert audit.inverse_verified
    assert audit.denominator == "a**2*p**2 + kappa**2"
    assert audit.topological_mass_squared == "kappa**2/a**2"


def test_gauge_ring_is_superficially_cubic_but_beta_not_claimed() -> None:
    audit = build_audit()
    assert audit.gauge_ring_superficial_degree == 3
    assert not audit.logarithmic_beta_extracted
    assert audit.verdict == "propagator_ready_tensor_integrals_not_evaluated"
