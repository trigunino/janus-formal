from __future__ import annotations

import unittest

import numpy as np

from janus_lab.particle_mesh_3d import (
    deposit_cloud_in_cell_3d,
    interpolate_cloud_in_cell_3d,
    leapfrog_particle_mesh_step_3d,
    particle_mesh_accelerations_3d,
    particle_mesh_fields_3d,
    wrap_periodic_position_3d,
)
from janus_lab.signed_sector import BodyState, Sector


class ParticleMesh3DTests(unittest.TestCase):
    def test_wrap_periodic_position_3d(self) -> None:
        wrapped = wrap_periodic_position_3d(np.asarray([1.2, -0.1, 0.5]), box_size=1.0)

        np.testing.assert_allclose(wrapped, np.asarray([0.2, 0.9, 0.5]))

    def test_deposit_cloud_in_cell_3d_conserves_sector_mass(self) -> None:
        bodies = [
            BodyState(np.asarray([0.125, 0.125, 0.125]), np.zeros(3), 2.0, Sector.POSITIVE),
            BodyState(np.asarray([0.625, 0.625, 0.625]), np.zeros(3), 3.0, Sector.NEGATIVE),
        ]

        positive, negative = deposit_cloud_in_cell_3d(bodies, (4, 4, 4), box_size=1.0)
        cell_volume = 1.0 / 64.0

        self.assertAlmostEqual(float(np.sum(positive) * cell_volume), 2.0)
        self.assertAlmostEqual(float(np.sum(negative) * cell_volume), 3.0)

    def test_interpolate_cloud_in_cell_3d_hits_cell_center(self) -> None:
        grid = np.arange(64, dtype=float).reshape(4, 4, 4)
        positions = [np.asarray([0.375, 0.625, 0.875])]

        interpolated = interpolate_cloud_in_cell_3d(grid, positions, box_size=1.0)

        self.assertAlmostEqual(interpolated[0], grid[1, 2, 3])

    def test_balanced_opposite_particles_cancel_3d_fields(self) -> None:
        bodies = [
            BodyState(np.asarray([0.375, 0.625, 0.5]), np.zeros(3), 1.0, Sector.POSITIVE),
            BodyState(np.asarray([0.375, 0.625, 0.5]), np.zeros(3), 1.0, Sector.NEGATIVE),
        ]

        fields = particle_mesh_fields_3d(bodies, (8, 8, 8), box_size=1.0)

        np.testing.assert_allclose(fields.potential_positive, 0.0, atol=1e-12)
        np.testing.assert_allclose(fields.potential_negative, 0.0, atol=1e-12)

    def test_opposite_sector_particle_mesh_3d_pair_separates(self) -> None:
        bodies = [
            BodyState(np.asarray([0.35, 0.5, 0.5]), np.zeros(3), 1.0, Sector.POSITIVE),
            BodyState(np.asarray([0.65, 0.5, 0.5]), np.zeros(3), 1.0, Sector.NEGATIVE),
        ]

        accelerations = particle_mesh_accelerations_3d(bodies, (16, 16, 16), box_size=1.0)

        self.assertLess(accelerations[0][0], 0.0)
        self.assertGreater(accelerations[1][0], 0.0)

    def test_leapfrog_particle_mesh_3d_wraps_positions(self) -> None:
        bodies = [
            BodyState(np.asarray([0.99, 0.5, 0.5]), np.asarray([1.0, 0.0, 0.0]), 1.0, Sector.POSITIVE),
            BodyState(np.asarray([0.99, 0.5, 0.5]), np.asarray([1.0, 0.0, 0.0]), 1.0, Sector.NEGATIVE),
        ]

        updated = leapfrog_particle_mesh_step_3d(bodies, 0.02, (8, 8, 8), box_size=1.0)

        self.assertLess(updated[0].position[0], 0.05)
        self.assertLess(updated[1].position[0], 0.05)


if __name__ == "__main__":
    unittest.main()
