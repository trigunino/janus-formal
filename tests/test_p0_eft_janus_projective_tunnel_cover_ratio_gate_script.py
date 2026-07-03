import unittest

from scripts.build_p0_eft_janus_projective_tunnel_cover_ratio_gate import build_payload


class P0EFTJanusProjectiveTunnelCoverRatioGateTests(unittest.TestCase):
    def test_projective_cover_ratio_closed_without_sheet_split_fit(self):
        payload = build_payload()

        self.assertTrue(payload["local_projective_tunnel_ratio_ready"])
        self.assertTrue(payload["local"]["throat_sigma_defined"])
        self.assertTrue(payload["local"]["two_fold_cover_survives_tunnel_surgery"])
        self.assertTrue(payload["global"]["global_cover_ratio_two_to_one_computed"])
        self.assertTrue(payload["global"]["global_cover_ratio_unique"])
        self.assertTrue(payload["global"]["cover_ratio_derived"])
        self.assertFalse(payload["global"]["phenomenological_sheet_split_inferred"])
        self.assertTrue(payload["global_projective_tunnel_ratio_closed"])


if __name__ == "__main__":
    unittest.main()
