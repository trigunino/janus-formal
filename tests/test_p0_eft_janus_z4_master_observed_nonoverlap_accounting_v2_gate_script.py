import unittest

from scripts.build_p0_eft_janus_z4_master_observed_nonoverlap_accounting_v2_gate import build_payload


class P0EFTJanusZ4MasterObservedNonOverlapAccountingV2GateTests(unittest.TestCase):
    def test_v2_accounting_never_promotes_directly(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-observed-nonoverlap-accounting-v2-gate")
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["observational_claim_allowed"])
        self.assertFalse(payload["full_planck_validation"])
        if payload["observed_trial_executed"]:
            self.assertTrue(payload["nonoverlap_accounting_performed"])
            self.assertIsNotNone(payload["nonoverlapping_total_combined_highl"])
            self.assertIsNotNone(payload["nonoverlapping_total_decomposed_highl"])
        else:
            self.assertFalse(payload["nonoverlap_accounting_performed"])
            self.assertEqual(payload["rejection_reason"], "observed_trial_not_executed")


if __name__ == "__main__":
    unittest.main()
