import unittest

from scripts.build_p0_eft_janus_z4_master_observed_failure_map_gate import build_payload


class P0EFTJanusZ4MasterObservedFailureMapGateTests(unittest.TestCase):
    def test_failure_map_blocks_promotion_and_identifies_highl(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-observed-failure-map-gate")
        if payload["observed_master_branch_rejected"]:
            self.assertEqual(payload["failure_class"], "high_l_acoustic_shape_failure")
            self.assertTrue(payload["highl_failure_dominates"])
            self.assertFalse(payload["candidate_promotion_allowed"])
            self.assertFalse(payload["observational_claim_allowed"])
            self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
