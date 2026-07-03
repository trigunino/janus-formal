import unittest

from scripts.build_p0_eft_janus_z2_sigma_tunnel_junction_radial_block_gate import build_payload


class P0EFTJanusZ2SigmaTunnelJunctionRadialBlockGateTests(unittest.TestCase):
    def test_tunnel_junction_radial_block_is_structurally_reduced(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["tunnel_junction_radial_ledger_declared"])
        self.assertTrue(payload["tunnel_junction_radial_block_reduced"])
        self.assertIn("[K_ab]", payload["structural_formula"])

    def test_tunnel_junction_of_a_waits_for_deltaK(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["DeltaK_of_a_ready"])
        self.assertFalse(payload["tunnel_junction_radial_block_of_a_ready"])
        self.assertIn("insert_active_DeltaK_s_of_a_and_DeltaK_tau_of_a", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
