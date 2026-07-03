import unittest

from scripts.build_p0_eft_janus_z2_sigma_tunnel_junction_flrw_reduction_gate import build_payload


class P0EFTJanusZ2SigmaTunnelJunctionFLRWReductionGateTests(unittest.TestCase):
    def test_junction_flrw_algebra_is_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["tunnel_junction_FLRW_algebra_ready"])
        self.assertTrue(payload["algebra"]["non_circular_use_of_junction_declared"])
        self.assertIn("DeltaK_s(a)", payload["formulas"]["rho_junction"])

    def test_junction_closure_still_needs_deltaK_and_partition(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["DeltaK_s_of_a_ready"])
        self.assertFalse(payload["closure"]["junction_rho_p_of_a_ready"])
        self.assertFalse(payload["tunnel_junction_FLRW_closure_ready"])
        self.assertIn(
            "define_non_circular_partition_between_CartanGHY_and_junction_source",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
