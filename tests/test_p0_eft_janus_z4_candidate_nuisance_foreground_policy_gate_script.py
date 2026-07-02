import unittest

from scripts.build_p0_eft_janus_z4_candidate_nuisance_foreground_policy_gate import build_payload


class P0EFTJanusZ4CandidateNuisanceForegroundPolicyGateTests(unittest.TestCase):
    def test_nuisance_policy(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-candidate-nuisance-foreground-policy-gate")
        self.assertTrue(payload["same_nuisance_vector_for_GR_and_candidate"])
        self.assertTrue(payload["foreground_parameters_declared_by_clik_wrappers"])
        self.assertTrue(payload["calibration_parameters_declared_by_clik_wrappers"])
        self.assertFalse(payload["global_nuisance_profiling_performed"])
        self.assertTrue(payload["candidate_result_conditional_on_component_reference_nuisance"])
        self.assertEqual(payload["candidate_status"], "fixed_nuisance_effective_candidate")
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])
        self.assertTrue(payload["policy_gate_passed"])


if __name__ == "__main__":
    unittest.main()
