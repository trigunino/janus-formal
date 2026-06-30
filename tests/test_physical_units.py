from __future__ import annotations

import unittest

import numpy as np

from janus_lab.physical_units import (
    PhysicalBoxCalibration,
    critical_density_msun_mpc3,
    hubble_si,
    hubble_time_gyr,
    minimum_grid_n_for_smoothing_radius,
    pm_dimensionless_velocities_to_km_s,
    pm_hubble_velocity_unit_km_s,
    pm_velocity_unit_km_s,
    sigma8_radius_mpc,
)


class PhysicalUnitsTests(unittest.TestCase):
    def test_hubble_si_is_positive(self) -> None:
        self.assertGreater(hubble_si(70.0), 0.0)

    def test_hubble_time_calibrates_pm_time_unit(self) -> None:
        self.assertAlmostEqual(hubble_time_gyr(70.0), 13.9684603, places=6)

    def test_critical_density_matches_standard_h_squared_scale(self) -> None:
        rho = critical_density_msun_mpc3(100.0)

        self.assertAlmostEqual(rho / 2.77537e11, 1.0, places=4)

    def test_box_calibration_mass_resolution(self) -> None:
        calibration = PhysicalBoxCalibration.from_total_absolute_omega(
            box_size_mpc=1000.0,
            grid_shape=(10, 10, 10),
            h0_km_s_mpc=70.0,
            omega_abs=0.315,
            positive_fraction=0.5,
        )

        self.assertEqual(calibration.particle_count_per_sector, 1000)
        self.assertEqual(calibration.cell_size_mpc, (100.0, 100.0, 100.0))
        self.assertAlmostEqual(
            calibration.positive_particle_mass_msun,
            calibration.negative_abs_particle_mass_msun,
        )
        self.assertGreater(
            calibration.nyquist_mode_inv_mpc,
            calibration.fundamental_mode_inv_mpc,
        )

    def test_sigma8_radius_uses_h_inverse_mpc(self) -> None:
        self.assertAlmostEqual(sigma8_radius_mpc(70.0), 8.0 / 0.7)

    def test_pm_velocity_unit_uses_explicit_time_scale(self) -> None:
        unit = pm_velocity_unit_km_s(box_size_mpc=1.0, time_unit_gyr=1.0)

        self.assertAlmostEqual(unit, 977.792, places=3)

    def test_pm_dimensionless_velocities_to_km_s(self) -> None:
        velocities = pm_dimensionless_velocities_to_km_s(
            np.asarray([[1.0, 0.0, 0.0], [0.0, 0.5, 0.0]]),
            box_size_mpc=1.0,
            time_unit_gyr=1.0,
        )

        np.testing.assert_allclose(
            velocities,
            np.asarray([[977.79222168, 0.0, 0.0], [0.0, 488.89611084, 0.0]]),
            rtol=1e-6,
        )

    def test_pm_hubble_velocity_unit_is_h0_box_speed(self) -> None:
        unit = pm_hubble_velocity_unit_km_s(box_size_mpc=1000.0, h0_km_s_mpc=70.0)

        self.assertAlmostEqual(unit, 70000.0, places=6)

    def test_smoothing_radius_resolution_requirement(self) -> None:
        radius = sigma8_radius_mpc(70.0)
        required = minimum_grid_n_for_smoothing_radius(
            box_size_mpc=1000.0,
            radius_mpc=radius,
            cells_per_radius=2.0,
        )

        self.assertEqual(required, 175)

    def test_box_reports_unresolved_sigma8_for_current_grid(self) -> None:
        calibration = PhysicalBoxCalibration.from_total_absolute_omega(
            box_size_mpc=1000.0,
            grid_shape=(8, 8, 8),
            h0_km_s_mpc=70.0,
            omega_abs=0.315,
            positive_fraction=0.5,
        )

        self.assertFalse(calibration.resolves_radius(calibration.sigma8_radius_mpc))
        self.assertEqual(
            calibration.grid_n_required_for_radius(calibration.sigma8_radius_mpc),
            175,
        )


if __name__ == "__main__":
    unittest.main()
