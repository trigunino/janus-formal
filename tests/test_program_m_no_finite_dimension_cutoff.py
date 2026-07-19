import numpy as np

from scripts.audit_program_m_no_finite_dimension_cutoff import (
    crown_order,
    remove_point,
    run_audit,
)
from scripts.program_m_dimension_two import polynomial_two_order_realizer


def test_crown_definition_is_a_partial_order() -> None:
    order = crown_order(5)
    assert np.all(np.diag(order))
    assert np.all((order.astype(int) @ order.astype(int) == 0) | order)


def test_crowns_are_point_minimal_obstructions() -> None:
    for half_size in range(3, 9):
        order = crown_order(half_size)
        assert polynomial_two_order_realizer(order) is None
        assert all(
            polynomial_two_order_realizer(remove_point(order, point)) is not None
            for point in range(len(order))
        )


def test_no_finite_cutoff_audit_passes() -> None:
    assert all(run_audit()["gates"].values())
