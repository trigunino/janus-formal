import numpy as np

from scripts.audit_program_m_scale_conformal import (
    PROTOCOL,
    consistency_from_points,
    poisson_sample,
    scale_conformal_audit,
    square_grid,
)


def test_poisson_sample_is_reproducible() -> None:
    assert poisson_sample(128, 12345) == poisson_sample(128, 12345)


def test_square_grids_exactly_collide_with_scale_identity() -> None:
    for density in PROTOCOL["physical_densities"]:
        report = consistency_from_points(square_grid(density))
        assert np.isclose(report["two_density_chain_scale_squared"], 1.0)
        assert np.isclose(report["absolute_distance_from_identity"], 0.0)


def test_conformal_protocol_retains_negative_control_failure() -> None:
    audit = scale_conformal_audit()
    assert audit["protocol_integrity"]["rank_matches"]
    assert not audit["negative_control_gate"]["all_square_grids_rejected"]
    assert all(row["square_grid_control"]["accepted"] for row in audit["rows"])
