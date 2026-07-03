import unittest

from scripts.build_p0_eft_janus_z2_sigma_bao_non_compressed_observation_gate import build_payload


class P0EFTJanusZ2SigmaBAONonCompressedObservationGateTests(unittest.TestCase):
    def test_desi_dr2_bao_data_are_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["bibliography_checked"])
        self.assertEqual(payload["data_points"], 13)
        self.assertEqual(payload["covariance_shape"], [13, 13])
        self.assertIn("DM_over_rs", payload["quantities"])
        self.assertTrue(payload["bao_observation_prerequisites_ready"])

    def test_bao_gate_waits_for_active_z2_sigma_prediction(self):
        payload = build_payload()

        self.assertFalse(payload["prediction"]["z2_sigma_bao_prediction_vector_ready"])
        self.assertFalse(payload["prediction"]["chi2_evaluated_against_desi_bao_covariance"])
        self.assertFalse(payload["bao_non_compressed_gate_passed"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertIn("compressed_planck_lcdm_rd", payload["forbidden_reuse"])


if __name__ == "__main__":
    unittest.main()
