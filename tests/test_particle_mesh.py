from __future__ import annotations

import unittest

import numpy as np

from janus_lab.particle_mesh import (
    deposit_cloud_in_cell,
    interpolate_cloud_in_cell,
    leapfrog_particle_mesh_step,
    mean_cross_sector_periodic_distance,
    mean_pairwise_periodic_distance,
    particle_mesh_accelerations,
    particle_mesh_fields,
    periodic_displacement,
    periodic_distance,
    segregation_metrics,
    wrap_periodic_position,
)
from janus_lab.signed_sector import BodyState, Sector


class ParticleMeshTests(unittest.TestCase):
    def test_wrap_periodic_position(self) -> None:
        wrapped = wrap_periodic_position(np.asarray([1.2, -0.1]), box_size=1.0)

        np.testing.assert_allclose(wrapped, np.asarray([0.2, 0.9]))

    def test_periodic_distance_uses_short_path(self) -> None:
        first = np.asarray([0.95, 0.5])
        second = np.asarray([0.05, 0.5])

        np.testing.assert_allclose(
            periodic_displacement(first, second, box_size=1.0),
            np.asarray([0.1, 0.0]),
        )
        self.assertAlmostEqual(periodic_distance(first, second, box_size=1.0), 0.1)

    def test_segregation_metrics(self) -> None:
        bodies = [
            BodyState(np.asarray([0.1, 0.5]), np.zeros(2), 1.0, Sector.POSITIVE),
            BodyState(np.asarray([0.2, 0.5]), np.zeros(2), 1.0, Sector.POSITIVE),
            BodyState(np.asarray([0.6, 0.5]), np.zeros(2), 1.0, Sector.NEGATIVE),
            BodyState(np.asarray([0.7, 0.5]), np.zeros(2), 1.0, Sector.NEGATIVE),
        ]

        self.assertAlmostEqual(
            mean_pairwise_periodic_distance(
                [bodies[0].position, bodies[1].position],
                box_size=1.0,
            ),
            0.1,
        )
        self.assertAlmostEqual(
            mean_cross_sector_periodic_distance(bodies, box_size=1.0),
            0.45,
        )
        self.assertAlmostEqual(segregation_metrics(bodies, box_size=1.0).segregation_ratio, 4.5)

    def test_deposit_cloud_in_cell_conserves_sector_mass(self) -> None:
        bodies = [
            BodyState(np.asarray([0.125, 0.125]), np.zeros(2), 2.0, Sector.POSITIVE),
            BodyState(np.asarray([0.625, 0.625]), np.zeros(2), 3.0, Sector.NEGATIVE),
        ]

        positive, negative = deposit_cloud_in_cell(bodies, (4, 4), box_size=1.0)
        cell_area = 1.0 / 16.0

        self.assertAlmostEqual(float(np.sum(positive) * cell_area), 2.0)
        self.assertAlmostEqual(float(np.sum(negative) * cell_area), 3.0)

    def test_interpolate_cloud_in_cell_hits_cell_center(self) -> None:
        grid = np.arange(16, dtype=float).reshape(4, 4)
        positions = [np.asarray([0.375, 0.625])]

        interpolated = interpolate_cloud_in_cell(grid, positions, box_size=1.0)

        self.assertAlmostEqual(interpolated[0], grid[1, 2])

    def test_balanced_opposite_particles_cancel_fields(self) -> None:
        bodies = [
            BodyState(np.asarray([0.375, 0.625]), np.zeros(2), 1.0, Sector.POSITIVE),
            BodyState(np.asarray([0.375, 0.625]), np.zeros(2), 1.0, Sector.NEGATIVE),
        ]

        fields = particle_mesh_fields(bodies, (16, 16), box_size=1.0)

        np.testing.assert_allclose(fields.potential_positive, 0.0, atol=1e-12)
        np.testing.assert_allclose(fields.potential_negative, 0.0, atol=1e-12)

    def test_opposite_sector_particle_mesh_pair_separates(self) -> None:
        bodies = [
            BodyState(np.asarray([0.35, 0.5]), np.zeros(2), 1.0, Sector.POSITIVE),
            BodyState(np.asarray([0.65, 0.5]), np.zeros(2), 1.0, Sector.NEGATIVE),
        ]

        accelerations = particle_mesh_accelerations(bodies, (32, 32), box_size=1.0)

        self.assertLess(accelerations[0][0], 0.0)
        self.assertGreater(accelerations[1][0], 0.0)

    def test_leapfrog_particle_mesh_wraps_positions(self) -> None:
        bodies = [
            BodyState(np.asarray([0.99, 0.5]), np.asarray([1.0, 0.0]), 1.0, Sector.POSITIVE),
            BodyState(np.asarray([0.99, 0.5]), np.asarray([1.0, 0.0]), 1.0, Sector.NEGATIVE),
        ]

        updated = leapfrog_particle_mesh_step(bodies, 0.02, (16, 16), box_size=1.0)

        self.assertLess(updated[0].position[0], 0.05)
        self.assertLess(updated[1].position[0], 0.05)


if __name__ == "__main__":
    unittest.main()
