import unittest

from scripts.build_p0_eft_janus_z2_sigma_oriented_pullback_variation_commutation_gate import build_payload


class P0EFTJanusZ2SigmaOrientedPullbackVariationCommutationGateTests(unittest.TestCase):
    def test_oriented_commutation_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["oriented_pullback_variation_commutation_ledger_declared"])
        self.assertTrue(payload["closure"]["fixed_map_commutation_ready"])
        self.assertTrue(payload["declared"]["projective_gluing_normal_orientation_sign_gate_declared"])
        self.assertIn("manual Sigma orientation sign", payload["forbidden"])

    def test_oriented_commutation_uses_projective_gluing_sign(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["z2_orientation_sign_fixed"])
        self.assertTrue(payload["closure"]["z2_oriented_commutation_ready"])
        self.assertTrue(payload["oriented_pullback_variation_commutation_ready"])
        self.assertIn("epsilon_Z2 = -1", payload["formulae"]["fixed_sign"])


if __name__ == "__main__":
    unittest.main()
