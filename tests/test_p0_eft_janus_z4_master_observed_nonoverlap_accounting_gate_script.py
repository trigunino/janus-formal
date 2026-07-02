import unittest

from scripts.build_p0_eft_janus_z4_master_observed_nonoverlap_accounting_gate import build_payload


class P0EFTJanusZ4MasterObservedNonOverlapAccountingGateTests(unittest.TestCase):
    def test_accounting_never_promotes_directly(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-observed-nonoverlap-accounting-gate")
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["observational_claim_allowed"])
        self.assertFalse(payload["full_planck_validation"])
        if payload["observed_trial_executed"]:
            self.assertTrue(payload["nonoverlap_accounting_performed"])
            self.assertIsNotNone(payload["nonoverlapping_total_combined_highl"])
            self.assertIsNotNone(payload["nonoverlapping_total_decomposed_highl"])


if __name__ == "__main__":
    unittest.main()
