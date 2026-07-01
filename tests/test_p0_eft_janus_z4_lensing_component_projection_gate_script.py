import unittest

from scripts.run_p0_eft_janus_z4_lensing_component_projection_gate import COMPONENTS, LAMBDAS, build_payload


class P0EFTJanusZ4LensingComponentProjectionGateTests(unittest.TestCase):
    def test_projection_gate_scaffold(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "janus-z4-lensing-component-projection-gate")
        self.assertEqual(payload["backend"], "camb_gr_plus_z4_delta")
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertEqual(tuple(payload["components"]), COMPONENTS)
        self.assertEqual(tuple(payload["lambda_grid"]), LAMBDAS)
        self.assertFalse(payload["official_likelihood_requested"])
        self.assertFalse(payload["official_likelihood_executed"])
        for component in COMPONENTS:
            self.assertIn(component, payload["response_stats"])
            self.assertIn(component, payload["trial"])
            self.assertIn("0.0", payload["trial"][component])
        self.assertFalse(payload["lensing_shape_delta_rescues_planck"])


if __name__ == "__main__":
    unittest.main()
