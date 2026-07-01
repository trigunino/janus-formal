from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_per_bin_nz_shift_audit import (
    build_payload,
    shifted_single_bin_rows,
)


class KiDS1000JanusHolstPerBinNzShiftAuditTests(unittest.TestCase):
    def test_shifted_single_bin_rows_adds_bin_specific_key(self) -> None:
        rows = [{"Z_MID": 0.2, "BIN1": 1.0}]

        shifted = shifted_single_bin_rows(rows, 2, 0.1)

        self.assertEqual(shifted[0]["Z_MID"], 0.2)
        self.assertAlmostEqual(shifted[0]["Z_MID_BIN2"], 0.3)

    def test_payload_scans_each_bin_and_shift(self) -> None:
        payload = build_payload(bins=[1, 2], shifts=[0.0, 0.05])

        self.assertEqual(len(payload["best_by_bin"]), 2)
        self.assertEqual(len(payload["rows"]), 4)
        self.assertFalse(payload["prediction_ready"])


if __name__ == "__main__":
    unittest.main()
