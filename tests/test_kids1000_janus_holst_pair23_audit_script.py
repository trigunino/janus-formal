from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_pair23_audit import build_payload, source_bin_stats, source_overlap


class KiDS1000JanusHolstPair23AuditTests(unittest.TestCase):
    def test_source_stats_and_overlap_are_finite(self) -> None:
        rows = [
            {"Z_MID": 0.1, "BIN1": 1.0, "BIN2": 1.0, "BIN3": 0.0, "BIN4": 0.0, "BIN5": 0.0},
            {"Z_MID": 0.2, "BIN1": 1.0, "BIN2": 1.0, "BIN3": 1.0, "BIN4": 0.0, "BIN5": 0.0},
            {"Z_MID": 0.3, "BIN1": 1.0, "BIN2": 0.0, "BIN3": 1.0, "BIN4": 0.0, "BIN5": 0.0},
        ]

        stats = source_bin_stats(rows, 2)
        overlap = source_overlap(rows, 2, 3)

        self.assertGreater(stats["z_mean"], 0.0)
        self.assertGreaterEqual(overlap, 0.0)

    def test_payload_audits_pair23_without_prediction_promotion(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["kernel_variant"], "angular_lens")
        self.assertEqual(payload["pair23_block"]["bin1"], 2)
        self.assertEqual(payload["pair23_block"]["bin2"], 3)
        self.assertEqual(len(payload["pair23_rows"]), 5)
        self.assertFalse(payload["prediction_ready"])


if __name__ == "__main__":
    unittest.main()
