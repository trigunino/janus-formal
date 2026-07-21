import numpy as np

from scripts.audit_program_m_branch_adversary import (
    branch_adversary_audit,
    repeated_two_level_branches,
)
from scripts.audit_program_m_exact_twins import largest_twin_class


def test_repeated_branches_form_partial_order_without_large_exact_twins() -> None:
    order = repeated_two_level_branches(6, 1234)
    assert np.all(np.diag(order))
    assert np.all(~(order & order.T) | np.eye(len(order), dtype=bool))
    assert np.all((order.astype(int) @ order.astype(int) > 0) <= order)
    assert largest_twin_class(order) <= 2


def test_repeated_branches_break_exact_twin_repair_on_fresh_seeds() -> None:
    audit = branch_adversary_audit()
    assert audit["total_all_four_collisions"] > 0
    assert audit["largest_passing_repeated_branch_family"] >= 6
    assert audit["status"] == "exact_twin_repair_broken_by_repeated_suborders"
