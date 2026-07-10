from __future__ import annotations

from scripts.audit_janus_terminal_hierarchy import build_audit


def test_terminal_hierarchy_orders_of_magnitude() -> None:
    audit = build_audit()

    assert audit.radius_to_planck_ratio > 1.0e60
    assert audit.primitive_planck_radius_m < 1.0e-34
    assert 1.0e121 < audit.required_flux_integer_if_planck_charge < 1.0e123
    assert 1.0e119 < audit.required_casimir_coefficient < 1.0e122
    assert 130.0 < audit.transmutation_exponent < 150.0
    assert 0.4 < audit.required_beta0_times_g_squared < 0.8
    assert 0.15 < audit.g_for_beta0_11 < 0.35
    assert 0.15 < audit.g_for_beta0_7 < 0.4


def test_hierarchy_audit_rejects_nonpositive_lengths() -> None:
    for target, planck in [(0.0, 1.0), (1.0, 0.0), (-1.0, 1.0)]:
        try:
            build_audit(target_radius_m=target, planck_length_m=planck)
        except ValueError:
            pass
        else:
            raise AssertionError("nonpositive length should be rejected")
