import numpy as np

from scripts.audit_program_m_interval_abundance import (
    PROTOCOL,
    interval_abundance_profile,
    run_audit,
)


def test_chain_interval_abundance_is_exact() -> None:
    chain = np.triu(np.ones((4, 4), dtype=bool))
    profile = interval_abundance_profile(chain, 2)
    assert np.allclose(profile, [0.5, 1 / 3, 1 / 6, 0])


def test_interval_profile_is_relabelling_invariant() -> None:
    chain = np.triu(np.ones((6, 6), dtype=bool))
    permutation = np.array([4, 0, 5, 2, 1, 3])
    relabelled = chain[np.ix_(permutation, permutation)]
    assert np.array_equal(
        interval_abundance_profile(chain, 4),
        interval_abundance_profile(relabelled, 4),
    )


def test_preregistered_interval_abundance_gates() -> None:
    audit = run_audit()
    assert audit["protocol"] == PROTOCOL
    assert audit["gates"]["all"] is True
