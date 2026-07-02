import unittest

from scripts.build_p0_eft_janus_z4_derived_slip_surface_orthogonality_gate import build_payload


class P0EFTJanusZ4DerivedSlipSurfaceOrthogonalityGateTests(unittest.TestCase):
    def test_surface_term_is_orthogonal_diagnostic_only(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-derived-slip-surface-orthogonality-gate")
        self.assertLess(payload["surface_term_parallel_fraction"], 0.50)
        self.assertGreater(payload["surface_term_perpendicular_fraction"], 0.50)
        self.assertTrue(payload["surface_term_is_orthogonal_diagnostic"])
        self.assertTrue(payload["full_derived_slip_archived"])
        self.assertIsNone(payload["orthogonal_residual_combined"])
        self.assertIsNone(payload["orthogonal_residual_decomposed"])
        self.assertIn("SurfaceSWConsistencyGate", payload["orthogonal_residual_reason"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
