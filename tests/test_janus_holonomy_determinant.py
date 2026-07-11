from __future__ import annotations

import math

from scripts.audit_janus_holonomy_determinant import (
    analytic_logdet_ratio,
    build_audit,
    truncated_logdet_ratio,
)


def test_quarter_holonomy_has_no_finite_stationary_point() -> None:
    audit = build_audit()

    assert audit.all_checks_pass
    assert abs(audit.quarter_cosine) < 1.0e-14
    assert audit.quarter_derivative_at_x1 < 0.0
    assert not audit.quarter_has_finite_stationary_point
    assert audit.product_ratio_error < 2.0e-4


def test_generic_interior_holonomy_and_mixed_sector_can_stabilize() -> None:
    audit = build_audit()

    assert math.isclose(audit.interior_stationary_x, math.log(2.0), rel_tol=1.0e-15)
    assert audit.interior_stationary_second_derivative > 0.0
    assert math.isclose(audit.mixed_stationary_exponential, 5.0, rel_tol=1.0e-15)
    assert audit.mixed_stationary_modulus_for_mass_sqrt2 > 0.0
    assert not audit.mixed_and_unweighted_moduli_equal


def test_finite_product_ratio_converges_to_analytic_holonomy_formula() -> None:
    finite = truncated_logdet_ratio(0.25, 1.7, 0.9, 1000)
    analytic = analytic_logdet_ratio(0.25, 1.7, 0.9)

    assert abs(finite - analytic) < 2.0e-4
