import numpy as np

from scripts.audit_program_m_count_fluctuations import (
    PROTOCOL,
    count_fano_factor,
    count_fluctuation_audit,
    poisson_fano,
)
from scripts.audit_program_m_scale_conformal import square_grid


def test_poisson_fano_is_reproducible() -> None:
    assert poisson_fano(128, 12345) == poisson_fano(128, 12345)


def test_square_grid_has_zero_equal_cell_dispersion() -> None:
    for density in PROTOCOL["physical_densities"]:
        assert np.isclose(count_fano_factor(square_grid(density)), 0.0)


def test_fresh_calibration_rejects_both_deterministic_controls() -> None:
    audit = count_fluctuation_audit()
    assert audit["negative_control_gate"]["all_square_grids_rejected"]
    assert audit["negative_control_gate"]["all_diagonal_controls_rejected"]
    assert audit["combined_with_mf_man_013"]["square_grid_rejected_by_fluctuations"]
