import numpy as np

from scripts.audit_program_m_weak_kernel_axioms import (
    is_partial_order,
    product_order,
    relabel,
    run_audit,
)


def test_product_order_is_intrinsic_under_relabelling_and_restriction() -> None:
    rng = np.random.default_rng(7)
    points = rng.random((12, 3))
    permutation = rng.permutation(12)
    order = product_order(points)
    assert is_partial_order(order)
    assert np.array_equal(product_order(points[permutation]), relabel(order, permutation))
    assert np.array_equal(product_order(points[:7]), order[:7, :7])


def test_weak_kernel_axioms_do_not_force_two_orders() -> None:
    report = run_audit()
    assert all(report["gates"].values())
    assert report["conclusion"].endswith("two-order representation")
