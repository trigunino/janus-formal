import unittest

from scripts.build_p0_eft_janus_z4_master_shape_regularization_gate import build_payload


class P0EFTJanusZ4MasterShapeRegularizationGateTests(unittest.TestCase):
    def test_regularization_clears_shape_lock_without_unlocking_planck(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-shape-regularization-gate")
        self.assertTrue(payload["pre_likelihood_lock_was_active"])
        self.assertFalse(payload["is_action_derived"])
        self.assertTrue(payload["shape_regularization_evaluated"])
        self.assertEqual(payload["zero_crossing_artifacts_after"], {})
        self.assertTrue(payload["shape_regularization_clears_pre_likelihood_lock"])
        self.assertLess(payload["carrier_parallel_fraction_after_regularization"], 0.7)
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["likelihood_evaluation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
