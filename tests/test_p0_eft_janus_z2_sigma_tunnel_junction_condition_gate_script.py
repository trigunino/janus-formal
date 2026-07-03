import unittest

from scripts.build_p0_eft_janus_z2_sigma_tunnel_junction_condition_gate import build_payload


class P0EFTJanusZ2SigmaTunnelJunctionConditionGateTests(unittest.TestCase):
    def test_tunnel_junction_condition_is_derived_from_sigma_stress(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["tunnel_junction_lock_closed"])
        self.assertTrue(payload["z2_tunnel_junction_condition_derived"])
        self.assertTrue(payload["lock"]["projected_sigma_stress_tensor_derived"])
        self.assertTrue(payload["lock"]["z2_orientation_reversal_included"])
        self.assertTrue(payload["legacy_lcdm_background_substitution_forbidden"])
        self.assertTrue(payload["archived_z4_junction_reuse_forbidden"])


if __name__ == "__main__":
    unittest.main()
