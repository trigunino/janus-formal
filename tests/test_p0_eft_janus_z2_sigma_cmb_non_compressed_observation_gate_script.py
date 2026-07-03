import unittest

from scripts.build_p0_eft_janus_z2_sigma_cmb_non_compressed_observation_gate import build_payload


class P0EFTJanusZ2SigmaCMBNonCompressedObservationGateTests(unittest.TestCase):
    def test_planck_non_compressed_likelihoods_are_available(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["bibliography_checked"])
        self.assertTrue(payload["prerequisites"]["planck_low_l_commander_available"])
        self.assertTrue(payload["prerequisites"]["planck_low_e_simall_available"])
        self.assertTrue(payload["prerequisites"]["planck_high_l_ttteee_available"])
        self.assertTrue(payload["prerequisites"]["planck_lensing_available"])
        self.assertTrue(payload["cmb_observation_prerequisites_ready"])

    def test_cmb_gate_waits_for_active_z2_sigma_spectra(self):
        payload = build_payload()

        self.assertFalse(payload["prediction"]["z2_sigma_cmb_theory_spectra_ready"])
        self.assertFalse(payload["prediction"]["planck_likelihood_evaluated_on_z2_sigma_spectra"])
        self.assertFalse(payload["cmb_non_compressed_gate_passed"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertIn("archived_z4_cmb_spectra", payload["forbidden_reuse"])


if __name__ == "__main__":
    unittest.main()
