from __future__ import annotations

import math

import pytest

from scripts.audit_janus_pe_jet_universality import (
    even_evaluator,
    exponential_difference_formula,
    finite_cover_order_bound,
    iterated_difference,
    odd_evaluator,
    sign_action,
)


def test_exponential_finite_difference_formula() -> None:
    for order in range(7):
        for x in (-2.0, -0.25, 0.0, 1.5):
            assert iterated_difference(math.exp, order, x) == pytest.approx(
                exponential_difference_formula(order, x),
                rel=2e-10,
                abs=2e-10,
            )


def test_exponential_never_passes_finite_difference_polynomial_test() -> None:
    for order in range(1, 8):
        assert iterated_difference(math.exp, order, 0.0) != 0.0


def test_finite_cover_order_bound() -> None:
    orders = [0, 1, 4, 2, 9]
    bound = finite_cover_order_bound(orders)
    assert all(order <= bound for order in orders)


def test_negative_order_rejected() -> None:
    with pytest.raises(ValueError):
        finite_cover_order_bound([0, -1, 2])
    with pytest.raises(ValueError):
        iterated_difference(math.exp, -1, 0.0)


def test_scalar_invariant_and_vector_covariant() -> None:
    for sign in (-1, 1):
        for jet_value in (-3.0, -1.0, 0.0, 2.0):
            assert even_evaluator(sign_action(sign, jet_value)) == even_evaluator(
                jet_value
            )
            assert odd_evaluator(sign_action(sign, jet_value)) == sign_action(
                sign, odd_evaluator(jet_value)
            )
