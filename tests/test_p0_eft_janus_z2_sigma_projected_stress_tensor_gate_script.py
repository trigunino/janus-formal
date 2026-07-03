import unittest

from scripts.build_p0_eft_janus_z2_sigma_projected_stress_tensor_gate import build_payload


class P0EFTJanusZ2SigmaProjectedStressTensorGateTests(unittest.TestCase):
    def test_projected_sigma_stress_tensor_is_derived_from_boundary_variation(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["projected_stress_tensor_lock_closed"])
        self.assertTrue(payload["projected_sigma_stress_tensor_derived"])
        self.assertTrue(payload["lock"]["boundary_action_variation_with_respect_to_induced_metric_declared"])
        self.assertTrue(payload["lock"]["z2_projection_to_visible_background_declared"])
        self.assertTrue(payload["legacy_lcdm_background_substitution_forbidden"])
        self.assertTrue(payload["archived_z4_background_reuse_forbidden"])


if __name__ == "__main__":
    unittest.main()
