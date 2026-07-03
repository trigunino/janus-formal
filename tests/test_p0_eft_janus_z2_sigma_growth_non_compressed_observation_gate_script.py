import unittest

from scripts.build_p0_eft_janus_z2_sigma_growth_non_compressed_observation_gate import build_payload


class P0EFTJanusZ2SigmaGrowthNonCompressedObservationGateTests(unittest.TestCase):
    def test_direct_sdss_eboss_growth_data_are_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["bibliography_checked"])
        self.assertEqual(payload["point_count"], 5)
        self.assertEqual(payload["covariance_shape"], [5, 5])
        self.assertTrue(payload["growth_observation_prerequisites_ready"])

    def test_growth_gate_waits_for_active_z2_sigma_prediction(self):
        payload = build_payload()

        self.assertFalse(payload["prediction"]["z2_sigma_growth_prediction_vector_ready"])
        self.assertFalse(payload["prediction"]["growth_prediction_vector_prerequisites_ready"])
        self.assertFalse(payload["prediction"]["chi2_evaluated_against_direct_fsigma8"])
        self.assertFalse(payload["growth_non_compressed_gate_passed"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertIn("archived_holst_membrane_branch_curve", payload["forbidden_reuse"])


if __name__ == "__main__":
    unittest.main()
