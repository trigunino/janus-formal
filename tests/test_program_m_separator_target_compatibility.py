import numpy as np

from scripts.audit_program_m_ensemble_separation import minkowski_order
from scripts.audit_program_m_separator_target_compatibility import (
    minimum_recursive_width,
    run_audit,
)


def test_minimum_width_returns_a_verified_small_integer() -> None:
    order = minkowski_order(10, np.random.default_rng(12))
    width = minimum_recursive_width(order)
    assert width is not None and 0 <= width <= 6


def test_fixed_width_two_is_not_target_compatible() -> None:
    assert all(run_audit()["gates"].values())
