import numpy as np

from scripts.audit_program_m_pattern_ladder import (
    canonical_mask,
    exact_minkowski_distribution,
    relation_mask,
    run_audit,
)


def test_exact_references_are_probabilities() -> None:
    for rank in range(2, 6):
        reference = exact_minkowski_distribution(rank)
        assert abs(sum(reference.values()) - 1.0) < 1e-12


def test_dynamic_pattern_code_is_relabeling_invariant() -> None:
    order = np.array(
        [[1, 1, 0], [0, 1, 0], [0, 0, 1]], dtype=bool
    )
    permutation = np.array([2, 0, 1])
    assert canonical_mask(3, relation_mask(order)) == canonical_mask(
        3, relation_mask(order[np.ix_(permutation, permutation)])
    )


def test_pattern_ladder_finds_a_separating_rank() -> None:
    audit = run_audit()
    assert audit["first_rank_with_zero_adversary_acceptance"] in audit["protocol"]["ranks"]
