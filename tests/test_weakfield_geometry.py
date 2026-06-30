from __future__ import annotations

import unittest

import numpy as np

from janus_lab.weakfield_geometry import (
    diagonal_tetrad_1p1,
    diagonal_tetrad_map_1p1,
    derivative_tetrad_map_1p1,
    dlog_weakfield_b4vol_1p1,
    gamma1_00_static_1d,
    max_lie_algebra_residual_1p1,
    max_lorentz_residual_1p1,
    metric_from_diagonal_tetrad_1p1,
    periodic_derivative_1d,
    slow_geodesic_acceleration_1d,
    weakfield_b4vol_1p1,
    weakfield_metric_1p1,
)


class WeakfieldGeometryTests(unittest.TestCase):
    def test_periodic_derivative_recovers_sine(self) -> None:
        n = 32
        box = 2.0 * np.pi
        x = np.arange(n) * box / n

        derivative = periodic_derivative_1d(np.cos(x), box)

        np.testing.assert_allclose(derivative, -np.sin(x), atol=1e-12)

    def test_tetrad_reconstructs_metric(self) -> None:
        phi = np.asarray([0.01, -0.01])
        psi = np.asarray([0.005, -0.005])
        metric = weakfield_metric_1p1(phi, psi)
        tetrad = diagonal_tetrad_1p1(metric)

        reconstructed = metric_from_diagonal_tetrad_1p1(tetrad)

        np.testing.assert_allclose(reconstructed, metric)

    def test_lgeom_tetrad_map_is_lorentz_only_for_equal_branch(self) -> None:
        phi = np.asarray([0.01, -0.01])
        equal_tetrad = diagonal_tetrad_1p1(weakfield_metric_1p1(phi))
        other_tetrad = diagonal_tetrad_1p1(weakfield_metric_1p1(-phi))

        equal_map = diagonal_tetrad_map_1p1(equal_tetrad, equal_tetrad)
        mismatched_map = diagonal_tetrad_map_1p1(equal_tetrad, other_tetrad)

        self.assertLess(max_lorentz_residual_1p1(equal_map), 1e-12)
        self.assertGreater(max_lorentz_residual_1p1(mismatched_map), 0.0)

    def test_lgeom_derivative_lie_algebra_residual_flags_mismatch(self) -> None:
        n = 32
        box = 2.0 * np.pi
        x = np.arange(n) * box / n
        phi = 1e-3 * np.cos(x)
        plus_tetrad = diagonal_tetrad_1p1(weakfield_metric_1p1(phi))
        equal_map = diagonal_tetrad_map_1p1(plus_tetrad, plus_tetrad)
        mismatch_map = diagonal_tetrad_map_1p1(plus_tetrad, diagonal_tetrad_1p1(weakfield_metric_1p1(-phi)))

        equal_dmap = derivative_tetrad_map_1p1(equal_map, box)
        mismatch_dmap = derivative_tetrad_map_1p1(mismatch_map, box)

        self.assertLess(max_lie_algebra_residual_1p1(equal_map, equal_dmap), 1e-12)
        self.assertGreater(max_lie_algebra_residual_1p1(mismatch_map, mismatch_dmap), 0.0)

    def test_slow_geodesic_acceleration_matches_negative_gradient_at_linear_order(self) -> None:
        n = 64
        box = 2.0 * np.pi
        x = np.arange(n) * box / n
        phi = 1e-4 * np.cos(x)

        acceleration = slow_geodesic_acceleration_1d(phi, np.zeros_like(phi), box)

        np.testing.assert_allclose(acceleration, 1e-4 * np.sin(x), atol=1e-12)

    def test_gamma_uses_spatial_metric_factor(self) -> None:
        phi = np.asarray([0.0, 0.01, 0.0, -0.01])
        psi = np.full_like(phi, 0.1)

        gamma = gamma1_00_static_1d(phi, psi, box_size=1.0)
        expected = periodic_derivative_1d(phi, 1.0) / (1.0 - 2.0 * psi)

        np.testing.assert_allclose(gamma, expected)

    def test_b4vol_is_positive_on_lorentzian_branch(self) -> None:
        phi = np.asarray([0.01, -0.01])

        b4 = weakfield_b4vol_1p1(phi)

        self.assertTrue(np.all(b4 > 0.0))

    def test_dlog_b4vol_matches_linear_phi_minus_psi_at_small_amplitude(self) -> None:
        n = 64
        box = 2.0 * np.pi
        x = np.arange(n) * box / n
        phi = 1e-6 * np.cos(x)
        psi = 0.25e-6 * np.cos(x)

        exact = dlog_weakfield_b4vol_1p1(phi, psi, box)
        linear = periodic_derivative_1d(phi - psi, box)

        np.testing.assert_allclose(exact, linear, atol=2e-12)


if __name__ == "__main__":
    unittest.main()
