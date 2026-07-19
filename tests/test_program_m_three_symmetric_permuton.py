import numpy as np

from scripts.audit_program_m_three_symmetric_permuton import (
    run_audit,
    three_symmetric_permuton_order,
)


def test_three_symmetric_permuton_is_a_partial_order() -> None:
    order = three_symmetric_permuton_order(32, np.random.default_rng(7))
    assert np.all(np.diag(order))
    assert np.all(~(order & order.T) | np.eye(len(order), dtype=bool))
    assert np.all((order.astype(int) @ order.astype(int) == 0) | order)


def test_three_symmetric_adversary_breaks_rank_three_gate_only_at_four() -> None:
    assert all(run_audit()["gates"].values())
