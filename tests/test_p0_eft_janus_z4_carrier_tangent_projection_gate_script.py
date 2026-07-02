import unittest

from scripts.build_p0_eft_janus_z4_carrier_tangent_projection_gate import build_payload


class P0EFTJanusZ4CarrierTangentProjectionGateTests(unittest.TestCase):
    def test_carrier_tangent_projection_runs(self):
        payload = build_payload(run_official=True)

        self.assertEqual(payload["status"], "janus-z4-carrier-tangent-projection-gate")
        self.assertTrue(payload["lambda_frozen"])
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["no_new_physics"])
        self.assertGreaterEqual(payload["z4_parallel_fraction_to_carrier_tangent"], 0.0)
        self.assertGreaterEqual(payload["z4_perpendicular_fraction_to_carrier_tangent"], 0.0)
        self.assertIn(payload["dominant_parallel_direction"], payload["parameter_steps"])
        self.assertIn("combined_highl", payload["orthogonal_residual_gain"])
        self.assertIn("decomposed_highl", payload["orthogonal_residual_gain"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
