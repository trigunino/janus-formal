import unittest

from scripts.build_p0_eft_janus_z2_tunnel_core_gate import build_payload


class P0EFTJanusZ2TunnelCoreGateTests(unittest.TestCase):
    def test_z2_tunnel_core_is_active_without_cyclic_z4(self):
        payload = build_payload()

        self.assertEqual(payload["active_geometry"], "Z2_projective_tunnel_sigma")
        self.assertTrue(payload["core"]["z2_cover_is_active_geometry"])
        self.assertTrue(payload["core"]["around_sigma_maps_to_z2_generator"])
        self.assertFalse(payload["core"]["cyclic_z4_required"])
        self.assertTrue(payload["core"]["z4_cmb_marked_non_evidence"])
        self.assertTrue(payload["z2_tunnel_core_closed"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
