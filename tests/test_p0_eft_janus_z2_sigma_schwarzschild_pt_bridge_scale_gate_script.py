import unittest

from scripts.build_p0_eft_janus_z2_sigma_schwarzschild_pt_bridge_scale_gate import (
    build_payload,
)


class SchwarzschildPTBridgeScaleGateTests(unittest.TestCase):
    def test_bridge_fixes_ratio_but_not_absolute_scale(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["local_result"]["R_Sigma_over_R_s"], 1.0)
        self.assertFalse(payload["absolute_RSigma_from_schwarzschild_bridge_ready"])
        self.assertFalse(payload["null_scale_gate"]["scale_selection_ready"])
        self.assertIn("Rs_absolute_scale_fixed", payload["blocked_by"])
        self.assertIn("mass_parameter_M_available", payload["blocked_by"])
        self.assertIn("regular_timelike_hK_pipeline_compatible", payload["blocked_by"])


if __name__ == "__main__":
    unittest.main()
