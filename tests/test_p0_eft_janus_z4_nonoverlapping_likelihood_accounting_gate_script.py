import unittest

from scripts.build_p0_eft_janus_z4_nonoverlapping_likelihood_accounting_gate import build_payload


class P0EFTJanusZ4NonOverlappingLikelihoodAccountingGateTests(unittest.TestCase):
    def test_nonoverlapping_accounting(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-nonoverlapping-likelihood-accounting-gate")
        self.assertTrue(payload["combined_highl_total_defined"])
        self.assertTrue(payload["decomposed_highl_total_defined"])
        self.assertTrue(payload["overlapping_highl_sum_forbidden"])
        self.assertTrue(payload["legacy_overlapping_total_marked_diagnostic_only"])
        self.assertLess(payload["nonoverlapping_total_combined_highl"], 0.0)
        self.assertLess(payload["nonoverlapping_total_decomposed_highl"], 0.0)
        self.assertTrue(payload["TE_standalone_cost_small"])
        self.assertTrue(payload["EE_standalone_not_degraded"])
        self.assertTrue(payload["accounting_gate_passed"])


if __name__ == "__main__":
    unittest.main()
