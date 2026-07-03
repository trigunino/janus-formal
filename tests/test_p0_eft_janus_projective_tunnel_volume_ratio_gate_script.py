import unittest

from scripts.build_p0_eft_janus_projective_tunnel_volume_ratio_gate import build_payload


class P0EFTJanusProjectiveTunnelVolumeRatioGateTests(unittest.TestCase):
    def test_degree_two_cover_fixes_cover_to_quotient_volume_ratio(self):
        payload = build_payload()

        self.assertTrue(payload["two_fold_cover_survives_tunnel_surgery"])
        self.assertTrue(payload["deck_invariant_volume_form_declared"])
        self.assertTrue(payload["quotient_measure_descends"])
        self.assertTrue(payload["cover_degree_equals_two"])
        self.assertTrue(payload["cover_to_quotient_volume_ratio_two"])
        self.assertTrue(payload["ratio_unique_by_cover_degree"])
        self.assertFalse(payload["phenomenological_sheet_split_inferred"])
        self.assertTrue(payload["projective_tunnel_cover_volume_ratio_closed"])


if __name__ == "__main__":
    unittest.main()
