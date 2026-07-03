import unittest

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_radial_block_gate import build_payload


class P0EFTJanusZ2SigmaCartanGHYRadialBlockGateTests(unittest.TestCase):
    def test_structural_cartan_ghy_radial_block_is_reduced(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["cartan_ghy_radial_ledger_declared"])
        self.assertTrue(payload["cartan_ghy_radial_block_reduced"])
        self.assertIn("partial_R K", payload["structural_formula"])

    def test_scale_factor_evaluation_still_requires_active_embedding(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["E_CartanGHY_of_a_ready"])
        self.assertTrue(payload["closure"]["R_Sigma_of_a_required"])
        self.assertFalse(payload["cartan_ghy_radial_block_of_a_ready"])
        self.assertIn("insert_active_R_Sigma_of_a", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
