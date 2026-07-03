import unittest

from scripts.build_p0_eft_janus_z2_sigma_fixed_map_pullback_variation_commutation_gate import build_payload


class P0EFTJanusZ2SigmaFixedMapPullbackVariationCommutationGateTests(unittest.TestCase):
    def test_fixed_map_pullback_commutation_is_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["fixed_map_pullback_variation_commutation_ledger_declared"])
        self.assertTrue(payload["closure"]["pullback_commutes_with_delta_omega_proved"])
        self.assertTrue(payload["fixed_map_pullback_variation_commutation_ready"])

    def test_commutation_excludes_map_variation(self):
        payload = build_payload()

        self.assertIn("delta_omega X_Sigma = 0", payload["formulae"]["fixed_map"])
        self.assertIn("X_Sigma^*(delta_omega omega)", payload["formulae"]["commutation"])
        self.assertIn("map variation term in delta omega", payload["forbidden"])
        self.assertIn("prove_z2_oriented_commutation", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
