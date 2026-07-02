import unittest

from scripts.build_p0_eft_janus_z4_local_cosmology_profiling_readiness_gate import build_payload


class P0EFTJanusZ4LocalCosmologyProfilingReadinessGateTests(unittest.TestCase):
    def test_readiness_blocks_until_source_level_delta_passes(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-local-cosmology-profiling-readiness-gate")
        self.assertTrue(payload["regenerative_GR_handshake_passed"])
        self.assertTrue(payload["cache_invalidation_passed"])
        self.assertTrue(payload["frozen_candidate_replay_passed"])
        self.assertTrue(payload["effective_z4_spectrum_deltas_regenerated_per_cosmology"])
        self.assertFalse(payload["source_level_z4_deltas_regenerated_per_cosmology"])
        self.assertFalse(payload["local_cosmology_profiling_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
