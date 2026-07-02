import unittest

from scripts.build_p0_eft_janus_z4_regenerative_frozen_candidate_replay_gate import build_payload


class P0EFTJanusZ4RegenerativeFrozenCandidateReplayGateTests(unittest.TestCase):
    def test_replay_schema_without_likelihoods(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "janus-z4-regenerative-frozen-candidate-replay-gate")
        self.assertEqual(payload["lambda_T"], -0.008)
        self.assertEqual(payload["lambda_E"], -0.02)
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["no_new_physics"])
        self.assertEqual(payload["z4_delta_source"], "reference_cosmology_replay")
        self.assertFalse(payload["z4_deltas_regenerated_per_cosmology"])
        self.assertFalse(payload["local_cosmology_profiling_allowed"])
        self.assertFalse(payload["checkpoint_replay_matches"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
