from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_nz_shift_scan import build_payload, shifted_nz_rows


class KiDS1000JanusHolstNzShiftScanTests(unittest.TestCase):
    def test_shifted_nz_rows_moves_redshift_midpoints(self) -> None:
        rows = [{"Z_MID": 0.2, "BIN1": 1.0}]

        shifted = shifted_nz_rows(rows, 0.1)

        self.assertAlmostEqual(shifted[0]["Z_MID"], 0.3)
        self.assertEqual(rows[0]["Z_MID"], 0.2)

    def test_payload_is_diagnostic_for_requested_shifts(self) -> None:
        payload = build_payload([0.0, 0.05])

        self.assertEqual(payload["dimension"], 75)
        self.assertEqual(len(payload["rows"]), 2)
        self.assertFalse(payload["prediction_ready"])


if __name__ == "__main__":
    unittest.main()
