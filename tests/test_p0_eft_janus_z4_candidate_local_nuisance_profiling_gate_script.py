import unittest

from scripts.build_p0_eft_janus_z4_candidate_local_nuisance_profiling_gate import build_payload


class P0EFTJanusZ4CandidateLocalNuisanceProfilingGateTests(unittest.TestCase):
    def test_local_nuisance_profiling_schema_without_running_cobaya(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "janus-z4-candidate-local-nuisance-profiling-gate")
        self.assertFalse(payload["run_official_requested"])
        self.assertTrue(payload["lambda_T_frozen"])
        self.assertTrue(payload["lambda_E_frozen"])
        self.assertTrue(payload["no_new_physics"])
        self.assertTrue(payload["same_optimizer_for_GR_and_candidate"])
        self.assertTrue(payload["same_priors_for_GR_and_candidate"])
        self.assertTrue(payload["same_bounds_for_GR_and_candidate"])
        self.assertTrue(payload["overlapping_total_forbidden"])
        self.assertTrue(payload["non_overlap_accounting"])
        self.assertFalse(payload["local_profiled_nuisance_effective_candidate"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
