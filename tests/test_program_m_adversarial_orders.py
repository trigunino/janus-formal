import numpy as np

from scripts.audit_program_m_adversarial_orders import (
    adversarial_order_audit,
    random_forward_dag,
)


def test_random_forward_dag_is_a_partial_order() -> None:
    order = random_forward_dag(32, 0.03, 1234)
    assert np.all(np.diag(order))
    assert np.all(~(order & order.T) | np.eye(len(order), dtype=bool))
    assert np.all((order.astype(int) @ order.astype(int) > 0) <= order)


def test_adversarial_generation_is_reproducible() -> None:
    assert np.array_equal(
        random_forward_dag(32, 0.03, 1234),
        random_forward_dag(32, 0.03, 1234),
    )


def test_combined_gate_survives_fresh_search_but_link_gate_does_not() -> None:
    audit = adversarial_order_audit()
    assert audit["totals"]["link_fluctuation_accepted"] > 0
    assert audit["first_link_only_collision"] is not None
    assert audit["totals"]["all_three_accepted"] == 0
    assert audit["first_combined_collision"] is None
