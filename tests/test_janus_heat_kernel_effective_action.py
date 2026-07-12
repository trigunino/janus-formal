from __future__ import annotations

import math

from scripts.audit_janus_heat_kernel_effective_action import (
    build_audit,
    direct_circle_heat_trace,
    poisson_circle_heat_trace,
)


def test_poisson_resummation_and_quarter_winding_structure() -> None:
    audit = build_audit()

    assert audit.all_checks_pass
    assert all(error < 1.0e-12 for error in audit.direct_poisson_errors)
    assert abs(audit.quarter_first_winding_weight) < 1.0e-14
    assert math.isclose(audit.quarter_second_winding_weight, -1.0)
    assert math.isclose(audit.antiperiodic_first_winding_weight, -1.0)
    assert 0.0 < audit.quarter_to_antiperiodic_leading_magnitude_ratio < 1.0


def test_local_heat_terms_are_affine_in_circle_modulus() -> None:
    audit = build_audit()

    assert abs(audit.local_action_midpoint_residual) < 1.0e-12


def test_finite_counterterm_can_fit_any_tested_target() -> None:
    audit = build_audit()

    assert audit.fitted_coefficients_are_distinct
    assert len(audit.counterterm_targets) >= 4
    assert all(
        target.fitted_local_coefficient > 0.0
        for target in audit.counterterm_targets
    )
    assert all(
        abs(target.derivative_at_target) < 1.0e-14
        for target in audit.counterterm_targets
    )
    assert all(
        target.curvature_at_target > 0.0
        for target in audit.counterterm_targets
    )


def test_direct_and_poisson_circle_heat_traces_match_independently() -> None:
    for holonomy in (0.0, 0.125, 0.25, 0.5):
        direct = direct_circle_heat_trace(4.1, 0.6, holonomy, cutoff=120)
        poisson = poisson_circle_heat_trace(4.1, 0.6, holonomy, cutoff=30)
        assert abs(direct - poisson) < 1.0e-12
