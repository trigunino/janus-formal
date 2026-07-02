import unittest

from scripts.build_p0_eft_janus_z4_derived_slip_surface_carrier_tangent_projection_gate import build_payload


class P0EFTJanusZ4DerivedSlipSurfaceCarrierTangentProjectionGateTests(unittest.TestCase):
    def test_surface_branch_is_weak_diagnostic_not_candidate(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-derived-slip-surface-carrier-tangent-projection-gate")
        self.assertEqual(payload["surface_branch_status"], "weak_orthogonal_diagnostic")
        self.assertGreaterEqual(payload["parallel_fraction_full_surface"], 0.70)
        self.assertLess(payload["parallel_fraction_full_surface"], 0.85)
        self.assertTrue(payload["doppler_reintroduces_carrier_tangency"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["diagnostic_surface_trial_allowed"])
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["no_free_doppler_amplitude"])
        self.assertTrue(payload["no_free_slip_parameter"])
        self.assertTrue(payload["no_free_eta_ratio"])
        self.assertTrue(payload["no_direct_Cl_patch"])
        self.assertTrue(payload["raw_toy_LOS_forbidden"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
