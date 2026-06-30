from __future__ import annotations

import unittest

import numpy as np

from janus_lab.vlasov_diagnostic import (
    advect_x_periodic,
    acceleration_from_potential_1d,
    gaussian_phase_space,
    lorentz_boost_1p1,
    lorentz_residual_1p1,
    minkowski_trace_1p1,
    phase_space_mass_with_weight,
    solve_periodic_poisson_1d,
    stress_energy_1p1,
    strang_step_periodic,
    transform_rank2_1p1,
    two_sector_vlasov_poisson_accelerations,
    two_sector_vlasov_poisson_step,
    total_mass,
    velocity_moments,
)


class VlasovDiagnosticTests(unittest.TestCase):
    def test_x_advection_shifts_by_one_cell(self) -> None:
        f = np.arange(8.0)[:, None]
        velocities = np.asarray([1.0])

        shifted = advect_x_periodic(f, velocities, dt=0.25, dx=0.25)

        np.testing.assert_allclose(shifted[:, 0], np.roll(f[:, 0], 1))

    def test_strang_step_conserves_mass_on_periodic_box(self) -> None:
        nx = 32
        nv = 16
        box = 1.0
        x = (np.arange(nx) + 0.5) * box / nx
        v = np.linspace(-1.0, 1.0, nv, endpoint=False)
        dx = box / nx
        dv = v[1] - v[0]
        f = gaussian_phase_space(x, v, x0=0.4, sigma_x=0.08, sigma_v=0.25, box_size=box)
        acceleration = 0.1 * np.sin(2.0 * np.pi * x)

        stepped = strang_step_periodic(f, v, acceleration, dt=0.02, dx=dx, dv=dv)

        self.assertGreaterEqual(float(np.min(stepped)), 0.0)
        self.assertAlmostEqual(total_mass(f, dx, dv), total_mass(stepped, dx, dv), places=12)

    def test_velocity_moments_for_symmetric_distribution(self) -> None:
        x = np.asarray([0.0, 0.5])
        v = np.asarray([-1.0, 0.0, 1.0])
        dv = 1.0
        f = np.asarray([[1.0, 2.0, 1.0], [2.0, 4.0, 2.0]])

        moments = velocity_moments(f, v, dv)

        np.testing.assert_allclose(moments["beta"], np.zeros(2))
        np.testing.assert_allclose(moments["P"], np.asarray([2.0, 4.0]))
        np.testing.assert_allclose(moments["Pi"], np.zeros(2))
        np.testing.assert_allclose(moments["Q"], np.zeros(2))

    def test_invalid_shapes_raise(self) -> None:
        with self.assertRaises(ValueError):
            advect_x_periodic(np.zeros((2, 2)), np.zeros(3), dt=1.0, dx=1.0)

    def test_periodic_poisson_1d_recovers_cosine(self) -> None:
        n = 32
        box_size = 2.0 * np.pi
        x = np.arange(n) * box_size / n
        expected = np.cos(x)
        density = -expected / (4.0 * np.pi)

        potential = solve_periodic_poisson_1d(density, box_size=box_size, subtract_mean=False)
        acceleration = acceleration_from_potential_1d(expected, box_size=box_size)

        np.testing.assert_allclose(potential, expected, atol=1e-12)
        np.testing.assert_allclose(acceleration, np.sin(x), atol=1e-12)

    def test_two_sector_accelerations_are_conjugate(self) -> None:
        nx = 16
        nv = 8
        box = 1.0
        x = (np.arange(nx) + 0.5) * box / nx
        v = np.linspace(-1.0, 1.0, nv, endpoint=False)
        dv = v[1] - v[0]
        plus = gaussian_phase_space(x, v, x0=0.3, sigma_x=0.08, sigma_v=0.3, box_size=box)
        minus = gaussian_phase_space(x, v, x0=0.7, sigma_x=0.08, sigma_v=0.3, box_size=box)

        a_plus, a_minus, effective_density = two_sector_vlasov_poisson_accelerations(
            plus,
            minus,
            v,
            dv,
            box_size=box,
        )

        np.testing.assert_allclose(a_plus, -a_minus, atol=1e-12)
        self.assertAlmostEqual(float(np.mean(effective_density)), 0.0, places=12)

    def test_two_sector_step_conserves_each_sector_mass(self) -> None:
        nx = 16
        nv = 8
        box = 1.0
        x = (np.arange(nx) + 0.5) * box / nx
        v = np.linspace(-1.0, 1.0, nv, endpoint=False)
        dx = box / nx
        dv = v[1] - v[0]
        plus = gaussian_phase_space(x, v, x0=0.3, sigma_x=0.08, sigma_v=0.3, box_size=box)
        minus = gaussian_phase_space(x, v, x0=0.7, sigma_x=0.08, sigma_v=0.3, box_size=box)

        stepped = two_sector_vlasov_poisson_step(plus, minus, v, dt=0.005, dx=dx, dv=dv, box_size=box)

        self.assertAlmostEqual(total_mass(plus, dx, dv), total_mass(stepped["positive"], dx, dv), places=12)
        self.assertAlmostEqual(total_mass(minus, dx, dv), total_mass(stepped["negative"], dx, dv), places=12)
        np.testing.assert_allclose(
            stepped["acceleration_positive"],
            -stepped["acceleration_negative"],
            atol=1e-12,
        )

    def test_phase_space_weight_is_explicit(self) -> None:
        f = np.ones((4, 3))
        weight = np.asarray([1.0, 2.0, 3.0, 4.0])

        unweighted = phase_space_mass_with_weight(f, dx=0.5, dv=0.25)
        weighted = phase_space_mass_with_weight(f, dx=0.5, dv=0.25, spatial_weight=weight)

        self.assertEqual(unweighted, 1.5)
        self.assertEqual(weighted, 3.75)

    def test_lorentz_boost_preserves_minkowski_trace(self) -> None:
        x = np.asarray([0.0, 0.5])
        v = np.asarray([-0.5, 0.0, 0.5])
        f = np.asarray([[1.0, 2.0, 1.0], [2.0, 4.0, 2.0]])
        boost = lorentz_boost_1p1(0.2)
        tensor = stress_energy_1p1(f, v, dv=0.5)

        transformed = transform_rank2_1p1(tensor, boost)

        self.assertLess(lorentz_residual_1p1(boost), 1e-12)
        self.assertAlmostEqual(minkowski_trace_1p1(tensor), minkowski_trace_1p1(transformed), places=12)


if __name__ == "__main__":
    unittest.main()
