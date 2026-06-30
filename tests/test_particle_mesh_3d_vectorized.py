from __future__ import annotations

import unittest

import numpy as np

from janus_lab.particle_mesh_3d import (
    deposit_cloud_in_cell_3d,
    particle_mesh_accelerations_3d,
)
from janus_lab.particle_mesh_3d_vectorized import (
    cosmological_pm_step_3d_vectorized,
    create_two_sector_lattice_state_3d,
    create_two_sector_lattice_state_from_displacements_3d,
    deposit_cloud_in_cell_3d_vectorized,
    deposit_sector_cloud_in_cell_3d_vectorized,
    estimate_vectorized_pm_memory_bytes,
    interpolate_cloud_in_cell_3d_vectorized,
    interpolate_vector_cloud_in_cell_3d_vectorized,
    particle_mesh_accelerations_3d_vectorized,
    vectorized_state_from_bodies,
)
from janus_lab.signed_sector import BodyState, Sector


class ParticleMesh3DVectorizedTests(unittest.TestCase):
    def test_vectorized_deposit_matches_object_deposit(self) -> None:
        bodies = [
            BodyState(np.asarray([0.125, 0.125, 0.125]), np.zeros(3), 2.0, Sector.POSITIVE),
            BodyState(np.asarray([0.625, 0.625, 0.625]), np.zeros(3), 3.0, Sector.NEGATIVE),
        ]
        state = vectorized_state_from_bodies(bodies)

        expected = deposit_cloud_in_cell_3d(bodies, (4, 4, 4), box_size=1.0)
        actual = deposit_cloud_in_cell_3d_vectorized(state, (4, 4, 4), box_size=1.0)

        np.testing.assert_allclose(actual[0], expected[0])
        np.testing.assert_allclose(actual[1], expected[1])

    def test_weighted_sector_deposit_matches_copied_state_deposit(self) -> None:
        state = create_two_sector_lattice_state_3d((3, 3, 3), box_size=1.0)
        negative = state.sector_signs == -1
        factors = np.ones(len(state.positions), dtype=float)
        factors[negative] = np.linspace(0.5, 1.5, int(np.sum(negative)))
        copied = state.copy()
        copied.mass_abs[negative] *= factors[negative]

        expected = deposit_cloud_in_cell_3d_vectorized(
            copied,
            (3, 3, 3),
            box_size=1.0,
        )[1]
        actual = deposit_sector_cloud_in_cell_3d_vectorized(
            state,
            -1,
            (3, 3, 3),
            box_size=1.0,
            particle_weight_factor=factors,
        )

        np.testing.assert_allclose(actual, expected)

    def test_vector_interpolation_matches_component_interpolation(self) -> None:
        positions = np.asarray(
            [
                [0.2, 0.3, 0.4],
                [0.8, 0.1, 0.6],
            ]
        )
        grids = tuple(
            np.arange(64, dtype=float).reshape(4, 4, 4) + offset
            for offset in (0.0, 100.0, 200.0)
        )

        expected = np.column_stack(
            [
                interpolate_cloud_in_cell_3d_vectorized(grid, positions, box_size=1.0)
                for grid in grids
            ]
        )
        actual = interpolate_vector_cloud_in_cell_3d_vectorized(
            grids,
            positions,
            box_size=1.0,
        )

        np.testing.assert_allclose(actual, expected)

    def test_vectorized_accelerations_match_object_accelerations(self) -> None:
        bodies = [
            BodyState(np.asarray([0.35, 0.5, 0.5]), np.zeros(3), 1.0, Sector.POSITIVE),
            BodyState(np.asarray([0.65, 0.5, 0.5]), np.zeros(3), 1.0, Sector.NEGATIVE),
        ]
        state = vectorized_state_from_bodies(bodies)

        expected = np.asarray(particle_mesh_accelerations_3d(bodies, (16, 16, 16), box_size=1.0))
        actual = particle_mesh_accelerations_3d_vectorized(state, (16, 16, 16), box_size=1.0)

        np.testing.assert_allclose(actual, expected, atol=1e-12)

    def test_vectorized_lattice_has_two_sectors(self) -> None:
        state = create_two_sector_lattice_state_3d((4, 4, 4), box_size=1.0)

        self.assertEqual(state.positions.shape, (128, 3))
        self.assertEqual(int(np.sum(state.sector_signs == 1)), 64)
        self.assertEqual(int(np.sum(state.sector_signs == -1)), 64)

    def test_vectorized_lattice_from_displacements_offsets_sectors(self) -> None:
        positive = np.zeros((2, 2, 2, 3))
        negative = np.zeros((2, 2, 2, 3))
        positive[..., 0] = 0.01
        negative[..., 0] = -0.01

        state = create_two_sector_lattice_state_from_displacements_3d(
            positive,
            negative,
            box_size=1.0,
        )

        np.testing.assert_allclose(state.positions[0], np.asarray([0.26, 0.25, 0.25]))
        np.testing.assert_allclose(state.positions[8], np.asarray([0.24, 0.25, 0.25]))

    def test_vectorized_cosmological_drag_damps_velocity(self) -> None:
        state = vectorized_state_from_bodies(
            [BodyState(np.asarray([0.5, 0.5, 0.5]), np.asarray([1.0, 0.0, 0.0]), 1.0, Sector.POSITIVE)]
        )

        updated = cosmological_pm_step_3d_vectorized(
            state,
            dt=0.1,
            scale_factor=1.0,
            expansion_rate=1.0,
            grid_shape=(8, 8, 8),
            box_size=1.0,
            gravity_scale=0.0,
        )

        np.testing.assert_allclose(updated.velocities[0], np.asarray([np.exp(-0.2), 0.0, 0.0]))

    def test_memory_estimate_is_positive(self) -> None:
        estimate = estimate_vectorized_pm_memory_bytes((16, 16, 16), particle_count=8192)

        self.assertGreater(estimate, 0)


if __name__ == "__main__":
    unittest.main()
