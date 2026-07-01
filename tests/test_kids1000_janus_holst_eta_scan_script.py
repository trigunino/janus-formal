from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_eta_scan import build_payload, default_eta_grid


class KiDS1000JanusHolstEtaScanTests(unittest.TestCase):
    def test_default_eta_grid_contains_current_branch(self) -> None:
        self.assertIn(-1.0, default_eta_grid())

    def test_payload_is_diagnostic_for_requested_eta_values(self) -> None:
        payload = build_payload([-1.0, 0.0])

        self.assertEqual(payload["dimension"], 75)
        self.assertEqual(len(payload["rows"]), 2)
        self.assertEqual(len(payload["best_pair_chi2_blocks"]), 15)
        self.assertEqual(len(payload["best_tomographic_max_bin_scan"]), 5)
        self.assertFalse(payload["prediction_ready"])


if __name__ == "__main__":
    unittest.main()
