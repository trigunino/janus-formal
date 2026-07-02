import unittest

from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import build_payload


class P0EFTJanusZ4DerivedSlipCarrierTangentProjectionGateTests(unittest.TestCase):
    def test_derived_slip_tangent_projection_is_diagnostic_only(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-derived-slip-carrier-tangent-projection-gate")
        self.assertTrue(payload["source_level_regeneration_gate_passed"])
        self.assertEqual(payload["visible_slip_projection"], "boundary_normal_derivative")
        self.assertEqual(payload["orientation_sign_policy"], "fixed_by_Z4_boundary_convention")
        self.assertTrue(payload["orientation_flip_diagnostic_only"])
        self.assertIn("orientation_flip_diagnostic", payload)
        self.assertGreaterEqual(payload["derived_slip_parallel_fraction"], 0.0)
        self.assertGreaterEqual(payload["derived_slip_perpendicular_fraction"], 0.0)
        self.assertLessEqual(payload["derived_slip_parallel_fraction"], 1.0 + 1.0e-9)
        self.assertIn(payload["dominant_tangent_direction"], payload["active_orientation"]["subchannels"]["full_slip_source"]["tangent_contribution_scores"])
        for key in ("surface_term", "early_isw_term", "polarization_Pi_term", "full_slip_source"):
            self.assertIn(key, payload["subchannel_projection"])
            self.assertIn("parallel_fraction", payload["subchannel_projection"][key])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
