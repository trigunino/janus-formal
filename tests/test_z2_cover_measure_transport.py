import unittest

from src.janus_lab.z2_cover_measure_transport import derive_measure_transport


def _payload() -> dict:
    return {
        "active_core": "JanusZ2CoverMasterAction",
        "source": "active_cover_metric_determinants",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "rho_eff_shortcut_used": False,
        "negative_thermodynamic_density_postulated": False,
        "full_no_fit_prediction_ready": False,
        "parameter_grid": [0.5, 1.0],
        "sqrt_abs_g_plus": [2.0, 4.0],
        "sqrt_abs_g_minus": [6.0, 2.0],
        "tau_jacobian_abs_minus_to_plus": [1.0, 2.0],
        "tau_jacobian_abs_plus_to_minus": [1.0, 0.5],
    }


class Z2CoverMeasureTransportTest(unittest.TestCase):
    def test_derives_measure_factors_from_determinants(self):
        out = derive_measure_transport(_payload())
        self.assertTrue(out["measure_transport_ready"])
        self.assertEqual(out["B_minus_to_plus"], [3.0, 1.0])
        self.assertEqual(out["B_plus_to_minus"], [1.0 / 3.0, 1.0])

    def test_rejects_rho_eff_shortcut(self):
        payload = _payload()
        payload["rho_eff_shortcut_used"] = True
        with self.assertRaisesRegex(ValueError, "rho_eff_shortcut_used"):
            derive_measure_transport(payload)


if __name__ == "__main__":
    unittest.main()
