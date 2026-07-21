import numpy as np

from scripts.audit_program_m_exact_twins import exact_twin_audit, largest_twin_class
from scripts.audit_program_m_twin_adversary import clone_vertex_order


def test_largest_twin_class_is_relabelling_invariant() -> None:
    order = clone_vertex_order(6, 1234)
    permutation = np.random.default_rng(8).permutation(len(order))
    assert largest_twin_class(order) == largest_twin_class(
        order[np.ix_(permutation, permutation)]
    )


def test_poisson_calibration_keeps_pairs_but_rejects_large_exact_clones() -> None:
    audit = exact_twin_audit()
    row = next(row for row in audit["rows"] if row["cardinality"] == 256)
    assert row["upper_threshold"] == 2
    assert all(not control["accepted"] for control in row["exact_clone_controls"])
