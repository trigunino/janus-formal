import unittest

from src.janus_lab.z2_cover_sigma_source import derive_sigma_source_from_alpha_h


def _payload() -> dict:
    return {
        "active_core": "JanusZ2CoverMasterAction",
        "source": "master_boundary_variation_alpha_h",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "rho_eff_shortcut_used": False,
        "negative_thermodynamic_density_postulated": False,
        "two_independent_actions_used": False,
        "full_no_fit_prediction_ready": False,
        "parameter_grid": [0.5, 1.0],
        "alpha_h_tau": [2.0, 3.0],
        "alpha_h_s": [5.0, 7.0],
        "sigma_orientation_plus": [1.0, 1.0],
        "sigma_orientation_minus": [-1.0, -1.0],
    }


class Z2CoverSigmaSourceTest(unittest.TestCase):
    def test_derives_sigma_source_from_metric_variation_alpha(self):
        out = derive_sigma_source_from_alpha_h(_payload())
        self.assertTrue(out["sigma_source_ready"])
        self.assertTrue(out["sigma_junction_derived"])
        self.assertEqual(out["J_Sigma_plus_tau"], [-4.0, -6.0])
        self.assertEqual(out["J_Sigma_minus_tau"], [4.0, 6.0])
        self.assertEqual(out["J_Sigma_plus_s"], [-10.0, -14.0])
        self.assertEqual(out["J_Sigma_minus_s"], [10.0, 14.0])

    def test_rejects_non_orientation_sign(self):
        payload = _payload()
        payload["sigma_orientation_minus"] = [0.0, -1.0]
        with self.assertRaisesRegex(ValueError, "orientation"):
            derive_sigma_source_from_alpha_h(payload)


if __name__ == "__main__":
    unittest.main()
