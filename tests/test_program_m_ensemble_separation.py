import numpy as np

from scripts.audit_program_m_ensemble_separation import (
    PROTOCOL,
    ensemble_statistics,
    matched_two_level_order,
    minkowski_order,
    run_audit,
)


def test_statistics_are_relabeling_and_orientation_invariant() -> None:
    order = minkowski_order(40, np.random.default_rng(12))
    permutation = np.random.default_rng(13).permutation(len(order))
    expected = ensemble_statistics(order)
    assert ensemble_statistics(order[np.ix_(permutation, permutation)]) == expected
    assert ensemble_statistics(order.T) == expected


def test_two_level_competitor_has_no_three_chain() -> None:
    order = matched_two_level_order(100, np.random.default_rng(14))
    assert ensemble_statistics(order)["three_chain_fraction"] == 0.0


def test_protocol_separates_training_and_validation_sizes() -> None:
    assert set(PROTOCOL["training_sizes"]).isdisjoint(
        PROTOCOL["failed_pilot_validation_sizes"]
    )
    assert set(PROTOCOL["training_sizes"]).isdisjoint(
        PROTOCOL["successor_validation_sizes"]
    )
    assert set(PROTOCOL["failed_pilot_validation_sizes"]).isdisjoint(
        PROTOCOL["successor_validation_sizes"]
    )


def test_preregistered_ensemble_audit_passes() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())
