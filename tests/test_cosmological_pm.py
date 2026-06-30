from __future__ import annotations

import unittest

import numpy as np

from janus_lab.cosmological_pm import (
    cosmological_pm_step,
    run_cosmological_pm,
    scale_factor_sequence,
)
from janus_lab.particle_mesh import leapfrog_particle_mesh_step
from janus_lab.signed_sector import BodyState, Sector


class CosmologicalPMTests(unittest.TestCase):
    def test_scale_factor_sequence_includes_endpoints(self) -> None:
        values = scale_factor_sequence(0.5, 1.0, 2)

        np.testing.assert_allclose(values, np.asarray([0.5, 0.75, 1.0]))

    def test_hubble_drag_damps_free_particle_velocity(self) -> None:
        body = BodyState(np.asarray([0.5, 0.5]), np.asarray([1.0, 0.0]), 1.0, Sector.POSITIVE)

        updated = cosmological_pm_step(
            [body],
            dt=0.1,
            scale_factor=1.0,
            expansion_rate=1.0,
            grid_shape=(8, 8),
            box_size=1.0,
            gravity_scale=0.0,
            hubble_drag=2.0,
        )[0]

        np.testing.assert_allclose(updated.velocity, np.asarray([np.exp(-0.2), 0.0]))

    def test_static_limit_matches_particle_mesh_step(self) -> None:
        bodies = [
            BodyState(np.asarray([0.35, 0.5]), np.zeros(2), 1.0, Sector.POSITIVE),
            BodyState(np.asarray([0.65, 0.5]), np.zeros(2), 1.0, Sector.NEGATIVE),
        ]

        static = leapfrog_particle_mesh_step(bodies, 0.0001, (32, 32), box_size=1.0)
        cosmological = cosmological_pm_step(
            bodies,
            dt=0.0001,
            scale_factor=1.0,
            expansion_rate=0.0,
            grid_shape=(32, 32),
            box_size=1.0,
        )

        for first, second in zip(static, cosmological):
            np.testing.assert_allclose(first.position, second.position)
            np.testing.assert_allclose(first.velocity, second.velocity)

    def test_run_cosmological_pm_returns_initial_plus_steps(self) -> None:
        body = BodyState(np.asarray([0.5, 0.5]), np.zeros(2), 1.0, Sector.POSITIVE)

        history = run_cosmological_pm(
            [body],
            dt=0.1,
            scale_factors=[0.5, 0.75, 1.0],
            expansion_rates=[1.0, 1.0, 1.0],
            grid_shape=(8, 8),
            box_size=1.0,
        )

        self.assertEqual(len(history), 3)


if __name__ == "__main__":
    unittest.main()
