from __future__ import annotations

from fractions import Fraction

import pytest

from scripts.audit_janus_low_order_jet_normal_forms import (
    AbelianConnectionOneJet,
    AbelianGaugeTwoJet,
    ImmersionSecondJet,
    alternating_part,
    apply_abelian_gauge_two_jet,
    curvature_matrix,
    is_symmetric,
    matrix_negate,
    normalize_abelian_connection_one_jet,
    normalize_immersion_second_jet,
    source_quadratic_change,
    symmetric_part,
    zero_matrix,
)


def test_immersion_second_jet_normalization() -> None:
    jet = ImmersionSecondJet(
        tangential=(
            (
                (Fraction(2), Fraction(-1)),
                (Fraction(-1), Fraction(3)),
            ),
            (
                (Fraction(0), Fraction(5, 2)),
                (Fraction(5, 2), Fraction(-4)),
            ),
        ),
        normal=(
            (
                (Fraction(7), Fraction(1)),
                (Fraction(1), Fraction(9)),
            ),
        ),
    )
    normalized, change = normalize_immersion_second_jet(jet)

    assert normalized.tangential == (zero_matrix(2, 2), zero_matrix(2, 2))
    assert normalized.normal == jet.normal
    assert source_quadratic_change(jet, change) == normalized


def test_immersion_source_change_preserves_normal_component() -> None:
    jet = ImmersionSecondJet(
        tangential=(((Fraction(1),),),),
        normal=(((Fraction(5),),),),
    )
    changed = source_quadratic_change(
        jet,
        (((Fraction(-3),),),),
    )
    assert changed.normal == jet.normal


def test_connection_normalization_retains_only_alternating_derivative() -> None:
    jet = AbelianConnectionOneJet(
        value=(Fraction(3), Fraction(-2)),
        derivative=(
            (Fraction(4), Fraction(7)),
            (Fraction(-1), Fraction(5)),
        ),
    )
    original_curvature = curvature_matrix(jet.derivative)
    normalized, gauge = normalize_abelian_connection_one_jet(jet)

    assert normalized.value == (Fraction(0), Fraction(0))
    assert normalized.derivative == alternating_part(jet.derivative)
    assert symmetric_part(normalized.derivative) == zero_matrix(2, 2)
    assert curvature_matrix(normalized.derivative) == original_curvature
    assert is_symmetric(gauge.hessian)


def test_symmetric_gauge_hessian_preserves_curvature() -> None:
    jet = AbelianConnectionOneJet(
        value=(Fraction(0), Fraction(1), Fraction(2)),
        derivative=(
            (Fraction(1), Fraction(2), Fraction(3)),
            (Fraction(4), Fraction(5), Fraction(6)),
            (Fraction(7), Fraction(8), Fraction(9)),
        ),
    )
    gauge = AbelianGaugeTwoJet(
        gradient=(Fraction(3), Fraction(4), Fraction(5)),
        hessian=(
            (Fraction(2), Fraction(-1), Fraction(4)),
            (Fraction(-1), Fraction(3), Fraction(0)),
            (Fraction(4), Fraction(0), Fraction(-5)),
        ),
    )
    transformed = apply_abelian_gauge_two_jet(jet, gauge)
    assert curvature_matrix(transformed.derivative) == curvature_matrix(jet.derivative)


def test_nonsymmetric_hessian_is_rejected() -> None:
    jet = AbelianConnectionOneJet(
        value=(Fraction(0), Fraction(0)),
        derivative=zero_matrix(2, 2),
    )
    bad_gauge = AbelianGaugeTwoJet(
        gradient=(Fraction(0), Fraction(0)),
        hessian=(
            (Fraction(0), Fraction(1)),
            (Fraction(0), Fraction(0)),
        ),
    )
    with pytest.raises(ValueError, match="symmetric"):
        apply_abelian_gauge_two_jet(jet, bad_gauge)


def test_normalizing_hessian_is_negative_symmetric_part() -> None:
    derivative = (
        (Fraction(1), Fraction(2)),
        (Fraction(5), Fraction(-3)),
    )
    jet = AbelianConnectionOneJet(
        value=(Fraction(8), Fraction(-1)),
        derivative=derivative,
    )
    _, gauge = normalize_abelian_connection_one_jet(jet)
    assert gauge.hessian == matrix_negate(symmetric_part(derivative))
