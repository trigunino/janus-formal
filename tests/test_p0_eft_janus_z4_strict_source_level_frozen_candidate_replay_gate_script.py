import unittest

from scripts.build_p0_eft_janus_z4_strict_source_level_frozen_candidate_replay_gate import build_payload


class P0EFTJanusZ4StrictSourceLevelFrozenCandidateReplayGateTests(unittest.TestCase):
    def test_strict_source_level_replay_matches_checkpoint(self):
        payload = build_payload(run_official=True)

        self.assertEqual(payload["status"], "janus-z4-strict-source-level-frozen-candidate-replay-gate")
        self.assertEqual(payload["z4_delta_source"], "strict_source_level_regenerated")
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["no_new_physics"])
        self.assertTrue(payload["delta_S_T_Z4_regenerated_per_cosmology"])
        self.assertTrue(payload["Pi_source_Z4_regenerated_per_cosmology"])
        self.assertTrue(payload["photon_polarization_hierarchy_regenerated_per_cosmology"])
        self.assertTrue(payload["source_level_z4_deltas_regenerated_per_cosmology"])
        self.assertTrue(payload["checkpoint_replay_matches"])
        self.assertTrue(payload["strict_source_level_frozen_candidate_replay_passed"])
        self.assertTrue(payload["TE_cost_small"])
        self.assertTrue(payload["EE_non_degraded"])
        self.assertTrue(payload["nonoverlap_accounting_only"])
        self.assertFalse(payload["local_cosmology_profiling_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
