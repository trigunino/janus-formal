import unittest

from scripts.build_p0_eft_janus_z4_candidate_local_cosmology_profiling_gate import build_payload


class P0EFTJanusZ4CandidateLocalCosmologyProfilingGateTests(unittest.TestCase):
    def test_local_cosmology_nuisance_profiling_runs_with_regenerative_backend(self):
        payload = build_payload(run_official=True)

        self.assertEqual(payload["status"], "janus-z4-candidate-local-cosmology-nuisance-profiling-gate")
        self.assertTrue(payload["readiness_gate_passed"])
        self.assertTrue(payload["same_cosmology_space_for_GR_and_candidate"])
        self.assertTrue(payload["same_priors_bounds_optimizer_for_GR_and_candidate"])
        self.assertTrue(payload["same_nuisance_policy_for_GR_and_candidate"])
        self.assertTrue(payload["lambda_T_frozen"])
        self.assertTrue(payload["lambda_E_frozen"])
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["overlapping_total_forbidden"])
        self.assertTrue(payload["non_overlap_accounting_only"])
        self.assertIsNotNone(payload["delta_chi2_profiled_combined_highl"])
        self.assertIsNotNone(payload["delta_chi2_profiled_decomposed_highl"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
