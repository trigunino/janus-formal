import unittest

from scripts.build_p0_eft_janus_z4_weak_surface_branch_diagnostic_closure_gate import build_payload


class P0EFTJanusZ4WeakSurfaceBranchDiagnosticClosureGateTests(unittest.TestCase):
    def test_weak_surface_branch_is_closed_after_refined_doppler(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-weak-surface-branch-diagnostic-closure-gate")
        self.assertTrue(payload["SW_surface_orthogonal_component_exists"])
        self.assertGreaterEqual(payload["physical_Doppler_completed_surface_parallel_fraction"], 0.70)
        self.assertTrue(payload["Doppler_completion_reintroduces_carrier_tangency"])
        self.assertTrue(payload["close_weak_surface_branch"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["diagnostic_surface_trial_allowed"])
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["no_free_Doppler_amplitude"])
        self.assertTrue(payload["no_free_slip_parameter"])
        self.assertTrue(payload["no_free_eta_ratio"])
        self.assertTrue(payload["no_direct_Cl_patch"])
        self.assertTrue(payload["raw_toy_LOS_forbidden"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
