import unittest

from scripts.build_p0_eft_janus_z4_boundary_safe_nuisance_profiling_gate import build_payload


class P0EFTJanusZ4BoundarySafeNuisanceProfilingGateTests(unittest.TestCase):
    def test_boundary_safe_schema_without_running_cobaya(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "janus-z4-boundary-safe-nuisance-profiling-gate")
        self.assertFalse(payload["run_official_requested"])
        self.assertTrue(payload["lambda_frozen"])
        self.assertTrue(payload["no_new_physics"])
        self.assertTrue(payload["non_overlap_accounting_only"])
        self.assertTrue(payload["same_nuisance_rule_for_GR_and_candidate"])
        self.assertFalse(payload["boundary_safe_local_profiled_candidate"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
