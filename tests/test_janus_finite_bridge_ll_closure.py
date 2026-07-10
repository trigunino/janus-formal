from __future__ import annotations

from scripts.audit_janus_finite_bridge_ll_closure import build_audit


def test_finite_bridge_ll_symbolic_audit() -> None:
    audit = build_audit()

    assert audit.all_symbolic_checks_pass
    assert audit.finite_sphere_combination == "-3*c2*(A*r**3 - Rs)"
    assert audit.horizon_radial_polynomial == "-A*r*(r - 1)*(r + 1)"
    assert audit.ll_field_invariant == "1/2"
    assert audit.primitive_flux_radius_law == "Eq(16*Rs**4*q**2, 1)"
    assert audit.charge_tension_relation == "q**2 = 256*chi**4*pi_c**4"


def test_planck_normalized_charge_is_planckian() -> None:
    audit = build_audit(target_radius_m=1.0e26)

    assert audit.required_q_inverse_m2 > 0.0
    assert audit.required_chi_inverse_m > 0.0
    assert audit.planck_q_gives_radius_m < 1.0e-34
    assert abs(audit.global_mass_constant_kg) > 1.0e52
