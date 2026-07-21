import numpy as np

from scripts.audit_program_m_ensemble_moment_adversary import antichain, total_order
from scripts.audit_program_m_ensemble_separation import minkowski_order
from scripts.audit_program_m_ergodic_layer_adversary import layered_order
from scripts.audit_program_m_height_growth import order_height, run_audit


def test_order_height_known_families() -> None:
    rng = np.random.default_rng(10)
    assert order_height(total_order(20, rng)) == 20
    assert order_height(antichain(20, rng)) == 1
    assert order_height(layered_order(500, rng)) <= 6


def test_height_is_relabeling_and_orientation_invariant() -> None:
    order = minkowski_order(80, np.random.default_rng(11))
    permutation = np.random.default_rng(12).permutation(len(order))
    expected = order_height(order)
    assert order_height(order[np.ix_(permutation, permutation)]) == expected
    assert order_height(order.T) == expected


def test_preregistered_height_audit_passes() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())

