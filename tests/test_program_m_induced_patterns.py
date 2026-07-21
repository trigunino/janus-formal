import numpy as np

from scripts.audit_program_m_induced_patterns import (
    canonical_mask,
    exact_minkowski_four_distribution,
    relation_mask,
    run_audit,
)


def test_exact_reference_has_all_sixteen_unlabelled_four_posets() -> None:
    reference = exact_minkowski_four_distribution()
    assert len(reference) == 16
    assert sum(reference.values()) == 1.0


def test_pattern_code_is_relabeling_invariant() -> None:
    order = np.array(
        [[1, 1, 0, 1], [0, 1, 0, 1], [0, 0, 1, 1], [0, 0, 0, 1]],
        dtype=bool,
    )
    permutation = np.array([2, 0, 3, 1])
    assert canonical_mask(relation_mask(order)) == canonical_mask(
        relation_mask(order[np.ix_(permutation, permutation)])
    )


def test_four_pattern_gate_separates_decorated_adversary() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())

