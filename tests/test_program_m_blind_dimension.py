import math

import numpy as np

from scripts.audit_program_m_blind_dimension import (
    PROTOCOL,
    myrheim_meyer_dimension,
    ordering_fraction,
    run_audit,
    theoretical_ordering_fraction,
)


def test_reference_ordering_fractions() -> None:
    assert abs(theoretical_ordering_fraction(1) - 1.0) < 1e-14
    assert abs(theoretical_ordering_fraction(2) - 0.5) < 1e-14


def test_chain_antichain_and_relabelling() -> None:
    chain = np.triu(np.ones((8, 8), dtype=bool))
    antichain = np.eye(8, dtype=bool)
    permutation = np.array([3, 0, 7, 2, 5, 1, 6, 4])
    relabelled = chain[np.ix_(permutation, permutation)]
    assert ordering_fraction(chain) == ordering_fraction(relabelled) == 1.0
    assert myrheim_meyer_dimension(chain) == 1.0
    assert math.isinf(myrheim_meyer_dimension(antichain))


def test_blind_validation_passes_preregistered_gate() -> None:
    audit = run_audit()
    assert audit["protocol"]["thresholds"] == PROTOCOL["thresholds"]
    assert audit["held_out_validation"]["gate"] is True
    grid = audit["controls"]["anisotropic_grid_24x24"]
    assert 1.7 < grid["estimated_dimension"] < 2.3
