from __future__ import annotations

import math

from scripts.audit_janus_finite_bridge_ll_closure import build_audit


def test_finite_bridge_ll_symbolic_audit() -> None:
    audit = build_audit()

    assert audit.all_symbolic_checks_pass
    assert audit.ll_field_invariant == "1/2"
    assert "A" in audit.finite_sphere_combination
    assert "Rs" in audit.finite_sphere_combination
    assert "r" in audit.horizon_radial_polynomial
    assert "256" in audit.charge_tension_relation


def test_planck_normalized_charge_is_planckian() -> None:
    audit = build_audit(target_radius_m=1.0e26)

    assert math.isclose(audit.required_q_inverse_m2, 2.5e-53, rel_tol=1.0e-12)
    assert audit.required_chi_inverse_m > 0.0
    assert audit.planck_q_gives_radius_m < 1.0e-34
    assert abs(audit.global_mass_constant_kg) > 1.0e52
