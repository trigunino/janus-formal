import unittest

from scripts.build_p0_eft_janus_projective_tunnel_cover_survival_gate import build_payload


class P0EFTJanusProjectiveTunnelCoverSurvivalGateTests(unittest.TestCase):
    def test_equivariant_tunnel_surgery_preserves_cover_but_not_global_ratio(self):
        payload = build_payload()

        self.assertTrue(payload["s4_to_rp4_cover_declared"])
        self.assertTrue(payload["tubular_replacement_equivariant"])
        self.assertTrue(payload["two_fold_cover_survives_tunnel_surgery"])
        self.assertTrue(payload["projective_cover_survival_closed"])
        self.assertFalse(payload["global_volume_ratio_computed"])
        self.assertFalse(payload["global_volume_ratio_unique"])
        self.assertFalse(payload["projective_tunnel_ratio_closed"])


if __name__ == "__main__":
    unittest.main()
