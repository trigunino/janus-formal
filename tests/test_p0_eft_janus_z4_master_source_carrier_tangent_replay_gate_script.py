import unittest

from scripts.build_p0_eft_janus_z4_master_source_carrier_tangent_replay_gate import build_payload


class P0EFTJanusZ4MasterSourceCarrierTangentReplayGateTests(unittest.TestCase):
    def test_source_replay_projects_without_unlocking_observation(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-source-carrier-tangent-replay-gate")
        self.assertTrue(payload["master_constraint_closure_audit_passed"])
        self.assertTrue(payload["source_level_payload_replayed"])
        self.assertEqual(payload["selected_master_ansatz"], "localized_transition")
        self.assertGreaterEqual(payload["parallel_fraction"], 0.0)
        self.assertGreaterEqual(payload["perpendicular_fraction"], 0.0)
        self.assertTrue(payload["all_channels_derived_from_same_U_Z4"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
