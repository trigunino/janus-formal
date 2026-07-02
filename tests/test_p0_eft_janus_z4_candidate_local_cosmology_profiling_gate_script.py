import unittest

from scripts.build_p0_eft_janus_z4_candidate_local_cosmology_profiling_gate import build_payload


class P0EFTJanusZ4CandidateLocalCosmologyProfilingGateTests(unittest.TestCase):
    def test_local_cosmology_profiling_is_blocked_without_regenerating_backend(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-candidate-local-cosmology-profiling-gate")
        self.assertTrue(payload["same_cosmology_space_for_GR_and_candidate"])
        self.assertTrue(payload["same_priors_bounds_optimizer_for_GR_and_candidate"])
        self.assertTrue(payload["lambda_frozen"])
        self.assertFalse(payload["cosmological_transfer_regeneration_available"])
        self.assertFalse(payload["local_cosmology_profiling_runnable"])
        self.assertFalse(payload["local_cosmology_profiling_executed"])
        self.assertFalse(payload["local_cosmology_profiled_candidate"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
