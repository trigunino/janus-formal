import unittest

from scripts.build_p0_eft_janus_z4_master_observed_failure_map_v2_gate import build_payload


class P0EFTJanusZ4MasterObservedFailureMapV2GateTests(unittest.TestCase):
    def test_failure_map_v2_blocks_promotion_and_identifies_highl(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-observed-failure-map-v2-gate")
        if payload["observed_master_v2_branch_rejected"]:
            self.assertEqual(payload["failure_class"], "high_l_acoustic_shape_failure")
            self.assertTrue(payload["highl_failure_dominates"])
            self.assertEqual(payload["dominant_failure_channel"], "highl_TTTEEE")
            self.assertFalse(payload["candidate_promotion_allowed"])
            self.assertFalse(payload["observational_claim_allowed"])
            self.assertFalse(payload["full_planck_validation"])
            self.assertFalse(payload["new_physics_allowed"])
            self.assertFalse(payload["retuning_allowed"])


if __name__ == "__main__":
    unittest.main()
