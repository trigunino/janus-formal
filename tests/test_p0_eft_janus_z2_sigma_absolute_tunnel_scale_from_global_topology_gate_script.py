import unittest

from scripts.build_p0_eft_janus_z2_sigma_absolute_tunnel_scale_from_global_topology_gate import (
    build_payload,
)


class AbsoluteTunnelScaleFromGlobalTopologyGateTests(unittest.TestCase):
    def test_topology_fixes_ratio_not_absolute_length(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["closure"]["projective_ratio_RSigma_over_ell_collar_fixed"])
        self.assertFalse(payload["closure"]["global_topology_has_dimensionful_scale"])
        self.assertFalse(payload["closure"]["absolute_RSigma_derived"])
        self.assertFalse(payload["absolute_scale_derivable_from_global_topology"])
        self.assertEqual(payload["ratio_result"]["R_Sigma_over_ell_collar"], 1.0)
        self.assertIn(
            "do_not_promote_stereographic_unit_radius_to_length",
            payload["forbidden_shortcuts"],
        )


if __name__ == "__main__":
    unittest.main()
