from __future__ import annotations

import math

from scripts.audit_janus_z4_dirac_alpha_lock import (
    build_audit,
    normalized_spectrum_numerator,
)


def test_primitive_z4_spectrum_has_unique_gap() -> None:
    audit = build_audit()

    assert audit.all_checks_pass
    assert audit.normalized_minimum == 1
    assert audit.minimizing_modes == [(0, 0)]
    assert normalized_spectrum_numerator(0, 0) == 1
    assert normalized_spectrum_numerator(1, 0) > 1
    assert normalized_spectrum_numerator(0, -1) > 1


def test_dirac_pair_derives_charge_and_alpha_ratio() -> None:
    audit = build_audit()

    assert math.isclose(
        audit.gap_squared_times_length_squared,
        1.0 / 8.0,
        rel_tol=1.0e-15,
    )
    assert math.isclose(
        audit.ll_charge_times_length_squared,
        1.0 / 4.0,
        rel_tol=1.0e-15,
    )
    assert math.isclose(
        audit.charge_to_sphere_gap_ratio,
        1.0 / 8.0,
        rel_tol=1.0e-15,
    )
    assert math.isclose(
        audit.alpha_over_geometry_length,
        1.0,
        rel_tol=1.0e-15,
    )


def test_pt_pair_cancels_eta_not_even_gap() -> None:
    audit = build_audit()

    assert math.isclose(audit.positive_fold_reduced_eta, 0.5)
    assert math.isclose(audit.negative_fold_reduced_eta, -0.5)
    assert math.isclose(audit.paired_reduced_eta, 0.0, abs_tol=1.0e-15)
    assert audit.ll_charge_times_length_squared > 0.0
