import numpy as np

from scripts.audit_program_m_projective_two_order_reconstruction import (
    realizes,
    restrict_permutation,
    run_audit,
)
from scripts.audit_program_m_two_order_representation import standard_example_s3, two_order_realizer_fast


def test_fast_realizer_and_restriction_on_product_order() -> None:
    rng = np.random.default_rng(8)
    points = rng.random((8, 2))
    order = np.all(points[:, None, :] <= points[None, :, :], axis=2)
    realizer = two_order_realizer_fast(order)
    assert realizer is not None and realizes(order, realizer)
    restricted = (restrict_permutation(realizer[0], 6), restrict_permutation(realizer[1], 6))
    assert realizes(order[:6, :6], restricted)


def test_fast_realizer_rejects_standard_s3() -> None:
    assert two_order_realizer_fast(standard_example_s3()) is None


def test_projective_reconstruction_audit_passes() -> None:
    assert all(run_audit()["gates"].values())
