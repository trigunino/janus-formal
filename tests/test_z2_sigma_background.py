import unittest

import numpy as np

from janus_lab.z2_sigma_background import (
    EffectiveFluidComponents,
    dimensionless_curvature_scale_from_h0_radius,
    make_dimensionless_hubble_from_effective_density,
    make_effective_fluid_functions,
    make_hubble_from_effective_density,
    omega_k_from_dimensionless_curvature_scale,
    omega_k_from_flrw_curvature_radius,
)


class Z2SigmaBackgroundTests(unittest.TestCase):
    def test_omega_k_builder_from_active_curvature_radius(self):
        h0 = 70.0
        radius = 3000.0
        open_value = omega_k_from_flrw_curvature_radius(h0, radius, -1)
        closed_value = omega_k_from_flrw_curvature_radius(h0, radius, 1)

        self.assertGreater(open_value, 0.0)
        self.assertLess(closed_value, 0.0)
        self.assertEqual(omega_k_from_flrw_curvature_radius(h0, radius, 0), 0.0)
        self.assertAlmostEqual(open_value, -closed_value)

    def test_omega_k_builder_rejects_invalid_curvature_inputs(self):
        with self.assertRaises(ValueError):
            omega_k_from_flrw_curvature_radius(0.0, 3000.0, -1)
        with self.assertRaises(ValueError):
            omega_k_from_flrw_curvature_radius(70.0, 0.0, -1)
        with self.assertRaises(ValueError):
            omega_k_from_flrw_curvature_radius(70.0, 3000.0, 2)

    def test_omega_k_builder_from_dimensionless_curvature_scale(self):
        open_value = omega_k_from_dimensionless_curvature_scale(2.0, -1)
        closed_value = omega_k_from_dimensionless_curvature_scale(2.0, 1)

        self.assertEqual(open_value, 0.25)
        self.assertEqual(closed_value, -0.25)
        self.assertEqual(omega_k_from_dimensionless_curvature_scale(2.0, 0), 0.0)
        with self.assertRaises(ValueError):
            omega_k_from_dimensionless_curvature_scale(0.0, 1)
        with self.assertRaises(ValueError):
            omega_k_from_dimensionless_curvature_scale(2.0, 2)

    def test_dimensionless_curvature_scale_from_h0_radius(self):
        value = dimensionless_curvature_scale_from_h0_radius(70.0, 3000.0)
        self.assertAlmostEqual(value, 70.0 * 3000.0 / 299_792.458)
        with self.assertRaises(ValueError):
            dimensionless_curvature_scale_from_h0_radius(0.0, 3000.0)
        with self.assertRaises(ValueError):
            dimensionless_curvature_scale_from_h0_radius(70.0, 0.0)

    def test_effective_fluid_assembler_requires_explicit_components(self):
        zero = lambda a: np.zeros_like(a)
        components = EffectiveFluidComponents(
            cartan_ghy_rho=lambda a: 0.2 / (a**3),
            cartan_ghy_p=zero,
            holst_nieh_yan_rho=lambda a: 0.1 / (a**4),
            holst_nieh_yan_p=lambda a: (0.1 / (a**4)) / 3.0,
            matter_flux_rho=zero,
            matter_flux_p=zero,
            counterterm_rho=lambda a: np.full_like(a, 0.7),
            counterterm_p=lambda a: np.full_like(a, -0.7),
        )
        rho_eff, p_eff = make_effective_fluid_functions(components)
        a = np.asarray([1.0, 0.5])

        self.assertEqual(rho_eff(a).shape, a.shape)
        self.assertEqual(p_eff(a).shape, a.shape)
        self.assertTrue(np.all(rho_eff(a) > 0.0))

    def test_hubble_builder_requires_explicit_active_density(self):
        rho = lambda a: 0.3 / (a**3) + 0.7
        h = make_hubble_from_effective_density(70.0, rho)
        e = make_dimensionless_hubble_from_effective_density(rho)
        z = np.asarray([0.0, 1.0, 2.0])

        values = h(z)

        self.assertEqual(values.shape, z.shape)
        self.assertTrue(np.all(values > 0.0))
        np.testing.assert_allclose(values / 70.0, e(z))

    def test_hubble_builder_rejects_unphysical_inputs(self):
        with self.assertRaises(ValueError):
            make_hubble_from_effective_density(0.0, lambda a: a)

        h = make_hubble_from_effective_density(70.0, lambda a: -np.ones_like(a))
        with self.assertRaises(ValueError):
            h(np.asarray([0.0]))

        h_shape = make_hubble_from_effective_density(70.0, lambda a: np.asarray([1.0]))
        with self.assertRaises(ValueError):
            h_shape(np.asarray([0.0, 1.0]))

        e_bad = make_dimensionless_hubble_from_effective_density(lambda a: -np.ones_like(a))
        with self.assertRaises(ValueError):
            e_bad(np.asarray([0.0]))

    def test_effective_fluid_assembler_rejects_bad_components(self):
        bad = lambda a: np.asarray([1.0])
        zero = lambda a: np.zeros_like(a)
        components = EffectiveFluidComponents(
            cartan_ghy_rho=bad,
            cartan_ghy_p=zero,
            holst_nieh_yan_rho=zero,
            holst_nieh_yan_p=zero,
            matter_flux_rho=zero,
            matter_flux_p=zero,
            counterterm_rho=zero,
            counterterm_p=zero,
        )
        rho_eff, _ = make_effective_fluid_functions(components)
        with self.assertRaises(ValueError):
            rho_eff(np.asarray([1.0, 0.5]))


if __name__ == "__main__":
    unittest.main()
