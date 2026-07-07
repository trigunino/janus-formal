import unittest

from scripts.build_p0_eft_janus_z2_sigma_boundary_lapse_normalization_gate import (
    build_payload,
)


class BoundaryLapseNormalizationGateTests(unittest.TestCase):
    def test_local_unit_lapse_is_ready_but_physical_lapse_is_not(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dimensionless_lapse_ready"])
        self.assertFalse(payload["physical_lapse_ready"])
        self.assertEqual(payload["local_result"]["N_boundary_unit_chart"], 1.0)
        self.assertIn("physical_time_scale_available", payload["blocked_by"])


if __name__ == "__main__":
    unittest.main()
