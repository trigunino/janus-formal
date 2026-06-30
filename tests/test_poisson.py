from __future__ import annotations

import unittest

import numpy as np

from janus_lab.poisson import (
    acceleration_from_potential_2d,
    acceleration_from_potential_3d,
    effective_density_grid,
    solve_periodic_poisson_2d,
    solve_periodic_poisson_3d,
)
from janus_lab.signed_sector import Sector


class PoissonTests(unittest.TestCase):
    def test_effective_density_grids_are_conjugate(self) -> None:
        positive = np.asarray([[1.0, 2.0], [3.0, 4.0]])
        negative = np.asarray([[0.5, 1.0], [1.5, 2.0]])

        plus = effective_density_grid(positive, negative, Sector.POSITIVE)
        minus = effective_density_grid(positive, negative, Sector.NEGATIVE)

        np.testing.assert_allclose(plus, -minus)
        np.testing.assert_allclose(plus, positive - negative)

    def test_periodic_poisson_recovers_cosine_potential(self) -> None:
        n = 32
        box_size = 2.0 * np.pi
        x = np.arange(n) * box_size / n
        y = np.arange(n) * box_size / n
        xx, yy = np.meshgrid(x, y, indexing="ij")
        expected_potential = np.cos(xx)
        density = -expected_potential / (4.0 * np.pi)

        potential = solve_periodic_poisson_2d(
            density,
            box_size=box_size,
            gravitational_constant=1.0,
            subtract_mean=False,
        )

        np.testing.assert_allclose(potential, expected_potential, atol=1e-12)

    def test_acceleration_is_negative_gradient(self) -> None:
        n = 32
        box_size = 2.0 * np.pi
        x = np.arange(n) * box_size / n
        y = np.arange(n) * box_size / n
        xx, _ = np.meshgrid(x, y, indexing="ij")
        potential = np.cos(xx)

        ax, ay = acceleration_from_potential_2d(potential, box_size=box_size)

        np.testing.assert_allclose(ax, np.sin(xx), atol=1e-12)
        np.testing.assert_allclose(ay, np.zeros_like(ay), atol=1e-12)

    def test_conjugate_sector_potentials_are_opposites(self) -> None:
        positive = np.zeros((16, 16))
        negative = np.zeros((16, 16))
        positive[4, 4] = 1.0
        negative[10, 10] = 0.5

        plus_density = effective_density_grid(positive, negative, Sector.POSITIVE)
        minus_density = effective_density_grid(positive, negative, Sector.NEGATIVE)
        plus_potential = solve_periodic_poisson_2d(plus_density, box_size=1.0)
        minus_potential = solve_periodic_poisson_2d(minus_density, box_size=1.0)

        np.testing.assert_allclose(plus_potential, -minus_potential, atol=1e-12)

    def test_periodic_poisson_3d_recovers_cosine_potential(self) -> None:
        n = 16
        box_size = 2.0 * np.pi
        x = np.arange(n) * box_size / n
        y = np.arange(n) * box_size / n
        z = np.arange(n) * box_size / n
        xx, _, _ = np.meshgrid(x, y, z, indexing="ij")
        expected_potential = np.cos(xx)
        density = -expected_potential / (4.0 * np.pi)

        potential = solve_periodic_poisson_3d(
            density,
            box_size=box_size,
            gravitational_constant=1.0,
            subtract_mean=False,
        )

        np.testing.assert_allclose(potential, expected_potential, atol=1e-12)

    def test_acceleration_3d_is_negative_gradient(self) -> None:
        n = 16
        box_size = 2.0 * np.pi
        x = np.arange(n) * box_size / n
        y = np.arange(n) * box_size / n
        z = np.arange(n) * box_size / n
        xx, _, _ = np.meshgrid(x, y, z, indexing="ij")
        potential = np.cos(xx)

        ax, ay, az = acceleration_from_potential_3d(potential, box_size=box_size)

        np.testing.assert_allclose(ax, np.sin(xx), atol=1e-12)
        np.testing.assert_allclose(ay, np.zeros_like(ay), atol=1e-12)
        np.testing.assert_allclose(az, np.zeros_like(az), atol=1e-12)

    def test_conjugate_sector_3d_potentials_are_opposites(self) -> None:
        positive = np.zeros((8, 8, 8))
        negative = np.zeros((8, 8, 8))
        positive[2, 2, 2] = 1.0
        negative[5, 5, 5] = 0.5

        plus_density = effective_density_grid(positive, negative, Sector.POSITIVE)
        minus_density = effective_density_grid(positive, negative, Sector.NEGATIVE)
        plus_potential = solve_periodic_poisson_3d(plus_density, box_size=1.0)
        minus_potential = solve_periodic_poisson_3d(minus_density, box_size=1.0)

        np.testing.assert_allclose(plus_potential, -minus_potential, atol=1e-12)


if __name__ == "__main__":
    unittest.main()
