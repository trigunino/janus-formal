import unittest

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_flrw_projection_gate import build_payload


class P0EFTJanusZ2SigmaCartanGHYFLRWProjectionGateTests(unittest.TestCase):
    def test_cartan_ghy_algebraic_projection_is_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["cartan_GHY_FLRW_algebraic_projection_ready"])
        self.assertTrue(payload["algebraic"]["rho_CartanGHY_formula_ready"])
        self.assertIn("DeltaK_s(a)", payload["formulas"]["rho_CartanGHY"])

    def test_scale_factor_embedding_functions_remain_open(self):
        payload = build_payload()

        self.assertFalse(payload["scale_factor"]["Delta_Ks_of_a_ready"])
        self.assertFalse(payload["scale_factor"]["Delta_Ktau_of_a_ready"])
        self.assertFalse(payload["cartan_GHY_FLRW_scale_factor_closure_ready"])
        self.assertIn("derive_DeltaK_s_of_a_from_Z2_tunnel_embedding", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
