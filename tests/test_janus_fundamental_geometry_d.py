from __future__ import annotations

import math

from scripts.audit_janus_fundamental_geometry_d import build_audit


def test_program_d_geometry_and_ratio_audit() -> None:
    audit = build_audit()

    assert audit.all_symbolic_checks_pass
    assert not audit.hopf_compatible_total_reversal_possible
    assert audit.cleared_alpha_ratio_residual == "0"
    assert math.isclose(
        audit.spectral_circle_modulus,
        math.sqrt(2.0) * math.pi,
        rel_tol=1.0e-15,
    )
    assert math.isclose(
        audit.alpha_over_geometry_length_unit_charge,
        1.0 / (2.0 * math.sqrt(2.0)),
        rel_tol=1.0e-15,
    )


def test_program_d_pin_patterns_are_distinct() -> None:
    audit = build_audit()

    assert audit.rp4_pin_plus
    assert not audit.rp4_pin_minus
    assert audit.twisted_hopf_pin_plus_if_target_classes_vanish
    assert audit.twisted_hopf_pin_minus_if_target_classes_vanish
