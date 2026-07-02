import unittest

from scripts.build_p0_eft_janus_z4_carrier_parameter_degeneracy_report import build_payload


class P0EFTJanusZ4CarrierParameterDegeneracyReportTests(unittest.TestCase):
    def test_omega_cdm_degeneracy_report(self):
        payload = build_payload(run_official=True)

        self.assertEqual(payload["status"], "janus-z4-carrier-parameter-degeneracy-report")
        self.assertEqual(payload["focus_parameter"], "omega_cdm")
        self.assertTrue(payload["lambda_frozen"])
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["no_new_physics"])
        self.assertFalse(payload["gain_survives_omega_cdm_marginalization"])
        self.assertIn("combined_highl", payload["summaries"])
        self.assertIn("decomposed_highl", payload["summaries"])
        self.assertGreater(
            payload["summaries"]["combined_highl"]["candidate_gain_after_marginalizing_omega_cdm"],
            0.0,
        )
        self.assertGreater(
            payload["summaries"]["decomposed_highl"]["candidate_gain_after_marginalizing_omega_cdm"],
            0.0,
        )
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
