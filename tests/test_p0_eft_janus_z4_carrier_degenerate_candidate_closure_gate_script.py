import unittest

from scripts.build_p0_eft_janus_z4_carrier_degenerate_candidate_closure_gate import build_payload


class P0EFTJanusZ4CarrierDegenerateCandidateClosureGateTests(unittest.TestCase):
    def test_carrier_degenerate_candidate_closure(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-carrier-degenerate-candidate-closure-gate")
        self.assertTrue(payload["fixed_carrier_robust_candidate"])
        self.assertTrue(payload["boundary_safe_nuisance_candidate"])
        self.assertTrue(payload["source_level_regenerative_candidate"])
        self.assertTrue(payload["local_carrier_profile_fails"])
        self.assertTrue(payload["carrier_tangent_projection_fails"])
        self.assertTrue(payload["orthogonal_residual_planck_bad"])
        self.assertTrue(payload["carrier_degenerate_effective_candidate"])
        self.assertEqual(payload["candidate_role"], "diagnostic_archived")
        self.assertFalse(payload["planck_candidate_role"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
