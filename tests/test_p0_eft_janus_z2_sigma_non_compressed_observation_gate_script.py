import unittest

from scripts.build_p0_eft_janus_z2_sigma_non_compressed_observation_gate import build_payload


class P0EFTJanusZ2SigmaNonCompressedObservationGateTests(unittest.TestCase):
    def test_full_no_fit_waits_for_non_compressed_observations(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["observation_equation_locks_closed"])
        self.assertTrue(payload["compressed_lcdm_validation_forbidden"])
        self.assertFalse(payload["non_compressed_observation_gates_passed"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertIn("compute_active_z2_sigma_growth_prediction_vector", payload["next_required"])
        self.assertIn("generate_active_z2_sigma_cmb_theory_spectra", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
