import unittest

from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_sobolev_index_gate import build_payload


class P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevIndexGateTests(unittest.TestCase):
    def test_sobolev_index_choice_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["sobolev_index_ledger_declared"])
        self.assertEqual(payload["index_choice"]["sigma_dimension"], 3)
        self.assertEqual(payload["index_choice"]["candidate_bulk_index"], "s_bulk >= 3")
        self.assertTrue(payload["declared"]["no_index_fit_to_observations"])

    def test_index_choice_remains_blocked_until_thresholds_are_proved(self):
        payload = build_payload()

        self.assertFalse(payload["obligations"]["candidate_indices_pass_trace_threshold"])
        self.assertFalse(payload["obligations"]["candidate_indices_pass_product_threshold"])
        self.assertFalse(payload["sobolev_index_ready"])
        self.assertIn("sobolev_index_choice_ready_for_trace_proof = false", payload["current_frontier"])


if __name__ == "__main__":
    unittest.main()
