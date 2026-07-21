import numpy as np

from scripts.audit_program_m_infinite_layer_adversary import (
    ATOM_LARGE,
    ATOM_SMALL,
    TAIL_MASS,
    infinite_layer_order,
    run_audit,
)


def test_analytic_moments_match_target() -> None:
    square_sum = ATOM_LARGE**2 + 3 * ATOM_SMALL**2 + (2 / 5) * TAIL_MASS**2
    cube_sum = ATOM_LARGE**3 + 3 * ATOM_SMALL**3 + (8 / 35) * TAIL_MASS**3
    assert abs(square_sum - 0.5) < 1e-12
    assert abs(cube_sum - 1 / 3) < 1e-12


def test_generator_is_a_partial_order() -> None:
    order = infinite_layer_order(200, np.random.default_rng(20))
    identity = np.eye(len(order), dtype=bool)
    assert np.all(np.diag(order))
    assert not np.any(order & order.T & ~identity)
    assert np.all((order @ order) <= order)


def test_infinite_layer_breaks_frozen_combined_gate() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())

