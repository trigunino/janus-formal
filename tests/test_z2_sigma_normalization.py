import unittest

import numpy as np

from janus_lab.physical_units import G_SI, critical_density_kg_m3
from janus_lab.z2_sigma_normalization import make_active_z2sigma_critical_normalization


class Z2SigmaNormalizationTests(unittest.TestCase):
    def test_active_critical_normalization_uses_explicit_h0(self):
        norm = make_active_z2sigma_critical_normalization(70.0)

        self.assertAlmostEqual(norm.rho_crit0_kg_m3, critical_density_kg_m3(70.0))
        self.assertAlmostEqual(norm.kappa_si, 8.0 * np.pi * G_SI)
        self.assertAlmostEqual(norm.kappa_rho_crit0_si, norm.kappa_si * norm.rho_crit0_kg_m3)

    def test_active_critical_normalization_supports_explicit_gravity_constant(self):
        norm = make_active_z2sigma_critical_normalization(70.0, gravitational_constant_si_z2sigma=2.0)

        self.assertAlmostEqual(norm.kappa_si, 16.0 * np.pi)
        self.assertAlmostEqual(
            norm.rho_crit0_kg_m3,
            critical_density_kg_m3(70.0) * G_SI / 2.0,
        )

    def test_kappa_rho_crit0_uses_same_explicit_gravity_constant(self):
        reference = make_active_z2sigma_critical_normalization(70.0)
        shifted_g = make_active_z2sigma_critical_normalization(
            70.0,
            gravitational_constant_si_z2sigma=2.0 * G_SI,
        )

        self.assertAlmostEqual(
            shifted_g.kappa_rho_crit0_si,
            reference.kappa_rho_crit0_si,
        )

    def test_active_critical_normalization_rejects_bad_inputs(self):
        with self.assertRaises(ValueError):
            make_active_z2sigma_critical_normalization(0.0)
        with self.assertRaises(ValueError):
            make_active_z2sigma_critical_normalization(70.0, gravitational_constant_si_z2sigma=0.0)


if __name__ == "__main__":
    unittest.main()
