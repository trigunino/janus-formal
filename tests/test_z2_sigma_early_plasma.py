import unittest

import numpy as np

from janus_lab.z2_sigma_early_plasma import (
    find_drag_epoch_bracket_z2sigma,
    make_baryon_mass_density_from_number_density_z2sigma,
    make_baryon_number_density_from_mass_density_z2sigma,
    make_blackbody_photon_energy_density_z2sigma,
    make_conserved_baryon_density_z2sigma,
    make_conserved_photon_density_z2sigma,
    make_conserved_photon_temperature_z2sigma,
    make_free_electron_density_z2sigma,
    make_drag_rate_over_h0_z2sigma,
    make_photon_baryon_sound_speed,
    make_photon_baryon_sound_speed_over_c,
    make_saha_ionization_fraction_z2sigma,
    make_thomson_drag_rate_z2sigma,
    solve_drag_epoch_z2sigma,
)


class Z2SigmaEarlyPlasmaTests(unittest.TestCase):
    def test_conserved_density_builders_use_active_normalizations(self):
        rho_b = make_conserved_baryon_density_z2sigma(2.0)
        rho_gamma = make_conserved_photon_density_z2sigma(3.0)
        z = np.asarray([0.0, 1.0])

        np.testing.assert_allclose(rho_b(z), [2.0, 16.0])
        np.testing.assert_allclose(rho_gamma(z), [3.0, 48.0])

    def test_conserved_photon_temperature_uses_active_normalization(self):
        temperature = make_conserved_photon_temperature_z2sigma(2.5)

        np.testing.assert_allclose(temperature(np.asarray([0.0, 3.0])), [2.5, 10.0])

    def test_free_electron_density_uses_active_ionization_history(self):
        n_e = make_free_electron_density_z2sigma(
            baryon_number_density_m3_z2sigma=lambda z: 10.0 * (1.0 + z) ** 3,
            ionization_fraction_z2sigma=lambda z: 0.25 * np.ones_like(z),
            electrons_per_baryon=0.8,
        )

        np.testing.assert_allclose(n_e(np.asarray([0.0, 1.0])), [2.0, 16.0])

    def test_saha_ionization_fraction_uses_active_baryon_and_temperature(self):
        x_e = make_saha_ionization_fraction_z2sigma(
            baryon_number_density_m3_z2sigma=lambda z: 1.0e9 * (1.0 + z) ** 3,
            photon_temperature_z2sigma=lambda z: 2.7255 * (1.0 + z),
            electron_mass_kg=9.1093837139e-31,
            boltzmann_constant_j_k=1.380649e-23,
            hbar_j_s=1.0545718176461565e-34,
            hydrogen_ionization_energy_j=13.598434599702 * 1.602176634e-19,
        )

        values = x_e(np.asarray([100.0, 1100.0, 3000.0]))

        self.assertEqual(values.shape, (3,))
        self.assertTrue(np.all(values >= 0.0))
        self.assertTrue(np.all(values <= 1.0))
        self.assertGreater(values[2], values[1])
        self.assertGreater(values[1], values[0])

    def test_saha_ionization_fraction_rejects_unphysical_inputs(self):
        with self.assertRaises(ValueError):
            make_saha_ionization_fraction_z2sigma(
                baryon_number_density_m3_z2sigma=lambda z: np.ones_like(z),
                photon_temperature_z2sigma=lambda z: np.ones_like(z),
                electron_mass_kg=0.0,
                boltzmann_constant_j_k=1.0,
                hbar_j_s=1.0,
                hydrogen_ionization_energy_j=1.0,
            )
        x_e = make_saha_ionization_fraction_z2sigma(
            baryon_number_density_m3_z2sigma=lambda z: -np.ones_like(z),
            photon_temperature_z2sigma=lambda z: np.ones_like(z),
            electron_mass_kg=1.0,
            boltzmann_constant_j_k=1.0,
            hbar_j_s=1.0,
            hydrogen_ionization_energy_j=1.0,
        )
        with self.assertRaises(ValueError):
            x_e(np.asarray([1.0]))

    def test_baryon_number_density_builder_uses_explicit_mass(self):
        n_b = make_baryon_number_density_from_mass_density_z2sigma(
            rho_baryon_mass_density_kg_m3_z2sigma=lambda z: np.asarray([2.0, 4.0]),
            baryon_mass_kg=2.0,
        )

        np.testing.assert_allclose(n_b(np.asarray([0.0, 1.0])), [1.0, 2.0])

    def test_baryon_mass_density_builder_uses_explicit_mass(self):
        rho_b = make_baryon_mass_density_from_number_density_z2sigma(
            baryon_number_density_m3_z2sigma=lambda z: np.asarray([1.0, 2.0]),
            baryon_mass_kg=3.0,
        )

        np.testing.assert_allclose(rho_b(np.asarray([0.0, 1.0])), [3.0, 6.0])

    def test_blackbody_photon_density_builder_uses_active_temperature(self):
        rho_gamma = make_blackbody_photon_energy_density_z2sigma(
            photon_temperature_z2sigma=lambda z: 2.0 * np.ones_like(z),
            radiation_constant_j_m3_k4=3.0,
        )

        np.testing.assert_allclose(rho_gamma(np.asarray([0.0, 1.0])), [48.0, 48.0])

    def test_density_builders_reject_unphysical_inputs(self):
        with self.assertRaises(ValueError):
            make_conserved_baryon_density_z2sigma(0.0)
        with self.assertRaises(ValueError):
            make_conserved_photon_density_z2sigma(-1.0)
        with self.assertRaises(ValueError):
            make_conserved_photon_temperature_z2sigma(0.0)
        n_e = make_free_electron_density_z2sigma(
            baryon_number_density_m3_z2sigma=lambda z: np.ones_like(z),
            ionization_fraction_z2sigma=lambda z: -np.ones_like(z),
            electrons_per_baryon=1.0,
        )
        with self.assertRaises(ValueError):
            n_e(np.asarray([1.0]))

        with self.assertRaises(ValueError):
            make_baryon_number_density_from_mass_density_z2sigma(
                lambda z: np.ones_like(z),
                baryon_mass_kg=0.0,
            )

        with self.assertRaises(ValueError):
            make_baryon_mass_density_from_number_density_z2sigma(
                lambda z: np.ones_like(z),
                baryon_mass_kg=0.0,
            )

        with self.assertRaises(ValueError):
            make_blackbody_photon_energy_density_z2sigma(
                lambda z: np.ones_like(z),
                radiation_constant_j_m3_k4=0.0,
            )

    def test_sound_speed_uses_supplied_active_densities(self):
        rho_b = lambda z: 0.05 * (1.0 + z) ** 3
        rho_gamma = lambda z: 5.0e-5 * (1.0 + z) ** 4
        cs = make_photon_baryon_sound_speed(rho_b, rho_gamma)
        values = cs(np.asarray([1000.0, 2000.0]))

        self.assertEqual(values.shape, (2,))
        self.assertTrue(np.all(values > 0.0))
        self.assertTrue(np.all(values < 299792.458))

    def test_sound_speed_over_c_matches_dimensional_sound_speed(self):
        rho_b = lambda z: 0.05 * (1.0 + z) ** 3
        rho_gamma = lambda z: 5.0e-5 * (1.0 + z) ** 4
        z = np.asarray([1000.0, 2000.0])
        cs = make_photon_baryon_sound_speed(rho_b, rho_gamma)
        cs_over_c = make_photon_baryon_sound_speed_over_c(rho_b, rho_gamma)

        np.testing.assert_allclose(cs_over_c(z), cs(z) / 299792.458)
        self.assertTrue(np.all(cs_over_c(z) > 0.0))
        self.assertTrue(np.all(cs_over_c(z) <= 1.0 / np.sqrt(3.0)))

    def test_sound_speed_rejects_unphysical_densities(self):
        cs = make_photon_baryon_sound_speed(
            lambda z: -np.ones_like(z),
            lambda z: np.ones_like(z),
        )
        with self.assertRaises(ValueError):
            cs(np.asarray([1.0]))

    def test_drag_epoch_solver_uses_supplied_active_rates(self):
        h = lambda z: np.full_like(z, 100.0, dtype=float)
        gamma = lambda z: 100.0 * (z / 1000.0)

        z_d = solve_drag_epoch_z2sigma(h, gamma, z_low=100.0, z_high=2000.0)

        self.assertAlmostEqual(z_d, 1000.0, places=9)

    def test_drag_epoch_solver_accepts_scale_free_rates(self):
        h0 = 70.0
        e = lambda z: np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7)
        h = lambda z: h0 * e(z)
        gamma = lambda z: h(z) * (z / 1000.0)
        gamma_over_h0 = make_drag_rate_over_h0_z2sigma(gamma, h0)

        z_d_dimensional = solve_drag_epoch_z2sigma(h, gamma, z_low=100.0, z_high=2000.0)
        z_d_scale_free = solve_drag_epoch_z2sigma(
            e,
            gamma_over_h0,
            z_low=100.0,
            z_high=2000.0,
        )

        self.assertAlmostEqual(z_d_scale_free, z_d_dimensional, places=9)
        self.assertAlmostEqual(z_d_scale_free, 1000.0, places=9)

    def test_drag_epoch_bracket_finder_uses_active_grid(self):
        h = lambda z: np.full_like(z, 100.0, dtype=float)
        gamma = lambda z: z / 10.0

        bracket = find_drag_epoch_bracket_z2sigma(h, gamma, [500.0, 900.0, 1100.0])

        self.assertEqual(bracket, (900.0, 1100.0))

    def test_drag_epoch_bracket_finder_rejects_missing_crossing(self):
        h = lambda z: np.full_like(z, 100.0, dtype=float)
        gamma = lambda z: np.full_like(z, 200.0, dtype=float)

        with self.assertRaises(ValueError):
            find_drag_epoch_bracket_z2sigma(h, gamma, [500.0, 900.0, 1100.0])

    def test_thomson_drag_rate_uses_active_free_electron_density(self):
        gamma = make_thomson_drag_rate_z2sigma(
            free_electron_density_m3_z2sigma=lambda z: 1.0e6 * np.ones_like(z),
            rho_baryon_z2sigma=lambda z: np.ones_like(z),
            rho_photon_z2sigma=lambda z: 10.0 * np.ones_like(z),
            sigma_thomson_m2=6.6524587321e-29,
        )
        values = gamma(np.asarray([900.0, 1100.0]))

        self.assertEqual(values.shape, (2,))
        self.assertTrue(np.all(values > 0.0))

    def test_thomson_drag_rate_rejects_unphysical_inputs(self):
        with self.assertRaises(ValueError):
            make_thomson_drag_rate_z2sigma(
                lambda z: np.ones_like(z),
                lambda z: np.ones_like(z),
                lambda z: np.ones_like(z),
                sigma_thomson_m2=0.0,
            )
        gamma = make_thomson_drag_rate_z2sigma(
            free_electron_density_m3_z2sigma=lambda z: -np.ones_like(z),
            rho_baryon_z2sigma=lambda z: np.ones_like(z),
            rho_photon_z2sigma=lambda z: np.ones_like(z),
            sigma_thomson_m2=1.0,
        )
        with self.assertRaises(ValueError):
            gamma(np.asarray([1000.0]))

    def test_drag_epoch_requires_valid_bracket(self):
        h = lambda z: np.full_like(z, 100.0, dtype=float)
        gamma = lambda z: np.full_like(z, 200.0, dtype=float)

        with self.assertRaises(ValueError):
            solve_drag_epoch_z2sigma(h, gamma, z_low=100.0, z_high=2000.0)


if __name__ == "__main__":
    unittest.main()
