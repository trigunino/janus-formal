from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_limber_xi_cosebis import build_payload


class KiDS1000JanusLimberXiCosebisTests(unittest.TestCase):
    def test_builds_same_order_vector_but_blocks_prediction_label(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["dimension"], 75)
        self.assertEqual(payload["tomographic_pair_count"], 15)
        self.assertTrue(payload["same_order_as_kids_en_scale_cut"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["chi2_ready"])
        self.assertEqual(payload["weyl_power_provenance"], "parametric_scaffold")


if __name__ == "__main__":
    unittest.main()
