import numpy as np

from scripts.audit_program_m_ergodic_layer_adversary import (
    LEVEL_WEIGHTS,
    layered_order,
    longest_strict_chain,
    run_audit,
)


def test_weights_match_both_target_moments() -> None:
    assert abs(float(np.sum(LEVEL_WEIGHTS**2)) - 0.5) < 1e-12
    assert abs(float(np.sum(LEVEL_WEIGHTS**3)) - 1 / 3) < 1e-12


def test_layered_generator_is_a_partial_order_with_bounded_height() -> None:
    order = layered_order(200, np.random.default_rng(5))
    assert np.all(np.diag(order))
    assert not np.any(order & order.T & ~np.eye(len(order), dtype=bool))
    assert np.all((order @ order) <= order)
    assert longest_strict_chain(order) <= len(LEVEL_WEIGHTS)


def test_ergodic_adversary_breaks_frozen_gate() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())

