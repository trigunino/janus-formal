import numpy as np

from scripts.audit_program_m_two_order_representation import (
    naturally_labelled_posets,
    standard_example_s3,
    two_order_realizer_fast,
)
from scripts.program_m_dimension_two import polynomial_two_order_realizer


def test_polynomial_recognizer_matches_exhaustive_through_six() -> None:
    for size in range(1, 7):
        for order in naturally_labelled_posets(size):
            assert (polynomial_two_order_realizer(order) is None) == (
                two_order_realizer_fast(order) is None
            )


def test_polynomial_recognizer_rejects_standard_s3() -> None:
    assert polynomial_two_order_realizer(standard_example_s3()) is None


def test_polynomial_recognizer_accepts_large_product_order() -> None:
    rng = np.random.default_rng(31)
    points = rng.random((64, 2))
    order = np.all(points[:, None, :] <= points[None, :, :], axis=2)
    assert polynomial_two_order_realizer(order) is not None
