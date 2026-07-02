import unittest

from scripts.build_p0_eft_janus_z4_master_action_normalization_v2_gate import build_payload


class P0EFTJanusZ4MasterActionNormalizationV2GateTests(unittest.TestCase):
    def test_v2_action_normalization_allows_handshake_only(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-action-normalization-v2-gate")
        self.assertTrue(payload["pre_likelihood_lock_v2_cleared"])
        self.assertEqual(payload["selected_revision"], "shared_U_norm_silk_guard")
        self.assertTrue(payload["shared_U_Z4_normalization_present"])
        self.assertTrue(payload["silk_guard_declared_upstream"])
        self.assertAlmostEqual(payload["normalization_parameter"], 2.0 / 3.0)
        self.assertTrue(payload["full_upstream_action_normalization_derived"])
        self.assertTrue(payload["action_normalization_v2_gate_passed"])
        self.assertTrue(payload["likelihood_handshake_allowed"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["likelihood_evaluation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
