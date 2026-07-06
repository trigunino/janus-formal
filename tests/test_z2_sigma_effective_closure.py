import unittest

from src.janus_lab.z2_sigma_effective_closure import validate_effective_closure_payload


def _payload():
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "effective_initial_data",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "full_no_fit_prediction_ready": False,
        "effective_initial_data": {
            "R_Sigma_over_ell_collar_Z2Sigma": 1.0,
            "projected_baryon_number_charge_Z2Sigma": 2.0,
        },
        "effective_initial_data_provenance": {
            "R_Sigma_over_ell_collar_Z2Sigma": "declared_effective_initial_data",
            "projected_baryon_number_charge_Z2Sigma": "declared_effective_initial_data",
        },
    }


class Z2SigmaEffectiveClosureTest(unittest.TestCase):
    def test_valid_effective_closure_is_canonicalized(self):
        payload = validate_effective_closure_payload(_payload())
        self.assertTrue(payload["effective_closure_ready"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertEqual(payload["effective_initial_data"]["R_Sigma_over_ell_collar_Z2Sigma"], 1.0)

    def test_forbids_planck_lcdm_z4_fit_provenance(self):
        for key in [
            "compressed_planck_lcdm_used",
            "archived_z4_reuse_used",
            "observational_fit_used",
        ]:
            payload = _payload()
            payload[key] = True
            with self.assertRaisesRegex(ValueError, "Forbidden provenance flag"):
                validate_effective_closure_payload(payload)

    def test_forbids_full_no_fit_claim(self):
        payload = _payload()
        payload["full_no_fit_prediction_ready"] = True
        with self.assertRaisesRegex(ValueError, "full_no_fit_prediction_ready=false"):
            validate_effective_closure_payload(payload)

    def test_rejects_deprecated_dimensionful_radius_closure(self):
        payload = _payload()
        payload["effective_initial_data"].pop("R_Sigma_over_ell_collar_Z2Sigma")
        payload["effective_initial_data"]["R_Sigma_effective_Mpc"] = 1.0
        payload["effective_initial_data_provenance"].pop(
            "R_Sigma_over_ell_collar_Z2Sigma"
        )
        payload["effective_initial_data_provenance"][
            "R_Sigma_effective_Mpc"
        ] = "declared_effective_initial_data"
        with self.assertRaisesRegex(ValueError, "R_Sigma_over_ell_collar_Z2Sigma"):
            validate_effective_closure_payload(payload)


if __name__ == "__main__":
    unittest.main()

