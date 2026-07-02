import unittest

from scripts.build_p0_eft_janus_z4_master_action_normalization_gate import build_payload


class P0EFTJanusZ4MasterActionNormalizationGateTests(unittest.TestCase):
    def test_action_normalization_allows_handshake_but_not_planck_trial(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-action-normalization-gate")
        self.assertTrue(payload["regularized_shape_report_gate_passed"])
        self.assertTrue(payload["regularized_shape_lock_cleared"])
        self.assertTrue(payload["membrane_transport_shape_available"])
        self.assertAlmostEqual(payload["normalization_parameter"], 2.0 / 3.0)
        self.assertTrue(payload["full_upstream_action_normalization_derived"])
        self.assertTrue(payload["action_normalization_gate_passed"])
        self.assertTrue(payload["likelihood_handshake_allowed"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
