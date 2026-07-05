import unittest

import numpy as np

from janus_lab.data import load_desi_bao
from janus_lab.z2_sigma_bao import (
    chi2_against_desi,
    chi2_against_desi_scale_free,
    comoving_distance_mpc,
    dimensionless_sound_ruler,
    predict_bao_quantity,
    prediction_vector_scale_free,
    prediction_vector,
    transverse_comoving_distance_mpc,
)
from janus_lab.z2_sigma_sound_ruler import evaluate_rd_z2sigma_mpc


class Z2SigmaBAOTests(unittest.TestCase):
    def test_strict_calculator_requires_positive_active_inputs(self):
        h = lambda z: np.full_like(z, 70.0, dtype=float)

        self.assertGreater(comoving_distance_mpc(0.5, h, samples=32), 0.0)
        with self.assertRaises(ValueError):
            predict_bao_quantity(0.5, "DM_over_rs", h, 0.0, samples=32)
        with self.assertRaises(ValueError):
            predict_bao_quantity(0.5, "BAD", h, 147.0, samples=32)

    def test_transverse_distance_supports_active_curvature(self):
        h = lambda z: np.full_like(z, 70.0, dtype=float)
        flat = transverse_comoving_distance_mpc(0.5, h, omega_k_z2sigma=0.0, samples=32)
        open_path = transverse_comoving_distance_mpc(0.5, h, omega_k_z2sigma=0.1, samples=32)
        closed_path = transverse_comoving_distance_mpc(0.5, h, omega_k_z2sigma=-0.1, samples=32)

        self.assertAlmostEqual(flat, comoving_distance_mpc(0.5, h, samples=32))
        self.assertGreater(open_path, flat)
        self.assertLess(closed_path, flat)

    def test_desi_vector_and_chi2_are_computable_when_active_functions_are_supplied(self):
        dataset = load_desi_bao()
        h = lambda z: 70.0 * np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7)

        vector = prediction_vector(dataset, h, 147.0, samples=64)
        result = chi2_against_desi(dataset, h, 147.0, samples=64)

        self.assertEqual(vector.shape, dataset.value.shape)
        self.assertEqual(result.prediction.shape, dataset.value.shape)
        self.assertTrue(np.isfinite(result.chi2))
        self.assertGreater(result.chi2, 0.0)

    def test_bao_ratios_are_invariant_under_common_hubble_scale(self):
        dataset = load_desi_bao()
        e_of_z = lambda z: np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7)
        cs = lambda z: np.full_like(z, 1.0e5, dtype=float)
        h_ref = lambda z: 70.0 * e_of_z(z)
        h_scaled = lambda z: 84.0 * e_of_z(z)
        rd_ref = evaluate_rd_z2sigma_mpc(h_ref, cs, 1050.0, z_max=1.0e5, samples=512)
        rd_scaled = evaluate_rd_z2sigma_mpc(
            h_scaled,
            cs,
            1050.0,
            z_max=1.0e5,
            samples=512,
        )

        np.testing.assert_allclose(rd_scaled, rd_ref * 70.0 / 84.0)
        np.testing.assert_allclose(
            prediction_vector(dataset, h_scaled, rd_scaled, samples=64),
            prediction_vector(dataset, h_ref, rd_ref, samples=64),
            rtol=1.0e-10,
            atol=1.0e-10,
        )

    def test_scale_free_bao_vector_matches_dimensional_vector(self):
        dataset = load_desi_bao()
        h0 = 72.0
        e_of_z = lambda z: np.sqrt(0.25 * (1.0 + z) ** 3 + 0.75)
        h = lambda z: h0 * e_of_z(z)
        cs_over_c = lambda z: np.full_like(z, 0.5, dtype=float)
        cs = lambda z: 299792.458 * cs_over_c(z)
        rd = evaluate_rd_z2sigma_mpc(h, cs, 1000.0, z_max=1.0e5, samples=512)
        rd_hat = dimensionless_sound_ruler(
            e_of_z,
            cs_over_c,
            1000.0,
            z_max=1.0e5,
            samples=512,
        )

        np.testing.assert_allclose(rd_hat, h0 * rd / 299792.458, rtol=1.0e-12)
        np.testing.assert_allclose(
            prediction_vector_scale_free(dataset, e_of_z, rd_hat, samples=64),
            prediction_vector(dataset, h, rd, samples=64),
            rtol=1.0e-10,
            atol=1.0e-10,
        )
        self.assertAlmostEqual(
            chi2_against_desi_scale_free(dataset, e_of_z, rd_hat, samples=64).chi2,
            chi2_against_desi(dataset, h, rd, samples=64).chi2,
        )


if __name__ == "__main__":
    unittest.main()
