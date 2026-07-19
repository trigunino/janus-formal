import numpy as np

from scripts.audit_program_m_intrinsic_link_fluctuations import (
    PROTOCOL,
    conditioned_poisson_order,
    intrinsic_link_fluctuation,
    intrinsic_link_fluctuation_audit,
)


def test_statistic_is_exactly_relabelling_invariant() -> None:
    order = conditioned_poisson_order(40, 1234)
    permutation = np.random.default_rng(9).permutation(len(order))
    relabelled = order[np.ix_(permutation, permutation)]
    assert np.isclose(
        intrinsic_link_fluctuation(order), intrinsic_link_fluctuation(relabelled)
    )


def test_statistic_is_exactly_orientation_reversal_invariant() -> None:
    order = conditioned_poisson_order(40, 1234)
    assert intrinsic_link_fluctuation(order) == intrinsic_link_fluctuation(order.T)


def test_intrinsic_gate_rejects_grids_and_chains() -> None:
    audit = intrinsic_link_fluctuation_audit()
    assert audit["negative_control_gate"]["all_square_grids_rejected"]
    assert audit["negative_control_gate"]["all_chains_rejected"]
    assert not audit["invariances"]["coordinates_used_by_statistic"]
    assert len(audit["rows"]) == len(PROTOCOL["cardinalities"])
