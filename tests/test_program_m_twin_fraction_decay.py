import numpy as np

from scripts.audit_program_m_exact_twins import largest_twin_class
from scripts.audit_program_m_infinite_layer_adversary import infinite_layer_order
from scripts.audit_program_m_twin_fraction_decay import run_audit


def test_twin_multiplicity_is_relabeling_and_orientation_invariant() -> None:
    order = infinite_layer_order(200, np.random.default_rng(30))
    permutation = np.random.default_rng(31).permutation(len(order))
    expected = largest_twin_class(order)
    assert largest_twin_class(order[np.ix_(permutation, permutation)]) == expected
    assert largest_twin_class(order.T) == expected


def test_preregistered_twin_fraction_audit_passes() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())

