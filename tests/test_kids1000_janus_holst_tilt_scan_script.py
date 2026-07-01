from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_tilt_scan import build_payload, default_tilt_grid


class KiDS1000JanusHolstTiltScanTests(unittest.TestCase):
    def test_default_tilt_grid_contains_current_shape(self) -> None:
        self.assertIn(1.0, default_tilt_grid())

    def test_payload_is_diagnostic_for_requested_tilts(self) -> None:
        payload = build_payload([0.0, 1.0])

        self.assertEqual(payload["dimension"], 75)
        self.assertEqual(len(payload["rows"]), 2)
        self.assertFalse(payload["prediction_ready"])


if __name__ == "__main__":
    unittest.main()
