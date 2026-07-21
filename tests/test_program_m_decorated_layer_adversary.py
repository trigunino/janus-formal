import numpy as np

from scripts.audit_program_m_decorated_layer_adversary import (
    ATOM_LARGE,
    ATOM_SMALL,
    MICRO_EDGE_PROBABILITY,
    TAIL_MASS,
    decorated_layer_order,
    run_audit,
)


def test_decorated_analytic_moments_match_target() -> None:
    p = MICRO_EDGE_PROBABILITY
    s2 = ATOM_LARGE**2 + 3 * ATOM_SMALL**2 + (2 / 5) * TAIL_MASS**2
    s3 = ATOM_LARGE**3 + 3 * ATOM_SMALL**3 + (8 / 35) * TAIL_MASS**3
    assert abs(1 - (1 - p / 2) * s2 - 0.5) < 1e-12
    assert abs(1 - 3 * s2 + 2 * s3 + (3 * p / 2) * (s2 - s3) - 1 / 6) < 1e-12


def test_decorated_generator_is_a_partial_order() -> None:
    order = decorated_layer_order(200, np.random.default_rng(40))
    identity = np.eye(len(order), dtype=bool)
    assert np.all(np.diag(order))
    assert not np.any(order & order.T & ~identity)
    assert np.all((order @ order) <= order)


def test_decorated_layer_breaks_frozen_four_diagnostic_gate() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())

