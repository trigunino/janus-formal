import numpy as np

from scripts.audit_program_m_twin_adversary import (
    clone_vertex_order,
    twin_adversary_audit,
    twin_classes,
)


def test_clone_construction_is_a_partial_order_with_named_twins() -> None:
    order = clone_vertex_order(6, 1234)
    assert np.all(np.diag(order))
    assert np.all(~(order & order.T) | np.eye(len(order), dtype=bool))
    assert np.all((order.astype(int) @ order.astype(int) > 0) <= order)
    assert len(twin_classes(order)[0]) >= 6


def test_twin_construction_is_reproducible() -> None:
    assert np.array_equal(clone_vertex_order(4, 1234), clone_vertex_order(4, 1234))


def test_engineered_twins_break_the_combined_gate_on_fresh_seeds() -> None:
    audit = twin_adversary_audit()
    assert audit["totals"]["all_three_accepted"] > 0
    assert audit["first_combined_collision"] is not None
    assert audit["largest_twin_class_in_a_three_gate_collision"] >= 10
    assert audit["status"] == "combined_order_only_gate_broken"
