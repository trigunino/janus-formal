import unittest

from scripts.build_p0_eft_janus_z4_highl_decomposed_candidate_promotion_gate import build_payload


class P0EFTJanusZ4HighLDecomposedCandidatePromotionGateTests(unittest.TestCase):
    def test_highl_decomposed_candidate_promotion(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-highl-decomposed-candidate-promotion-gate")
        self.assertTrue(payload["GR_handshake_TE_EE_passed"])
        self.assertTrue(payload["frozen_candidate_invariant"])
        self.assertTrue(payload["no_retuning"])
        self.assertTrue(payload["combined_highl_total_improves"])
        self.assertTrue(payload["decomposed_highl_total_improves"])
        self.assertTrue(payload["TE_standalone_cost_small"])
        self.assertTrue(payload["EE_standalone_not_degraded"])
        self.assertTrue(payload["planck_highl_decomposed_effective_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
