from __future__ import annotations

import math

from scripts.audit_janus_dirac_spectral_geometry import (
    alpha_over_sphere_radius,
    build_audit,
    determinant_amplitude,
    monopole_gap_squared_times_l2,
    zero_mode_eta,
)


def test_primitive_monopole_dirac_data() -> None:
    audit = build_audit()

    assert audit.all_checks_pass
    assert audit.zero_mode_multiplicity == 1
    assert audit.first_nonzero_gap_squared_times_l2 == 2
    assert math.isclose(audit.alpha_over_sphere_radius, 1.0)
    assert audit.bimetric_selected_monopole_magnitude == 1


def test_half_holonomy_is_eta_neutral_and_determinant_maximal() -> None:
    audit = build_audit()

    assert math.isclose(audit.half_holonomy_eta, 0.0, abs_tol=1.0e-15)
    assert math.isclose(
        audit.half_holonomy_determinant_amplitude,
        2.0,
        rel_tol=1.0e-15,
    )
    assert determinant_amplitude(0.5) >= determinant_amplitude(0.25)
    assert math.isclose(zero_mode_eta(1, 0.8), -zero_mode_eta(1, 0.2))


def test_circle_ratio_is_not_the_alpha_ratio() -> None:
    audit = build_audit()

    assert math.isclose(
        audit.circle_radius_over_sphere_radius,
        1.0 / (2.0 * math.sqrt(2.0)),
        rel_tol=1.0e-15,
    )
    assert math.isclose(audit.alpha_over_sphere_radius, 1.0)
    assert not math.isclose(
        audit.circle_radius_over_sphere_radius,
        audit.alpha_over_sphere_radius,
    )


def test_general_monopole_bimetric_selection() -> None:
    assert monopole_gap_squared_times_l2(1, 0) == 0
    assert monopole_gap_squared_times_l2(1, 1) == 2
    assert alpha_over_sphere_radius(1) == 1.0
    assert alpha_over_sphere_radius(2) < 1.0
    assert alpha_over_sphere_radius(0) > 1.0
