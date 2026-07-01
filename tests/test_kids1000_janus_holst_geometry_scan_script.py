from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_geometry_scan import (
    build_payload,
    default_q0_grid,
    max_source_redshift,
    retained_source_fractions,
)


class KiDS1000JanusHolstGeometryScanTests(unittest.TestCase):
    def test_default_q0_grid_contains_current_geometry(self) -> None:
        self.assertIn(-0.087, default_q0_grid())

    def test_max_source_redshift_reads_z_mid(self) -> None:
        self.assertEqual(max_source_redshift([{"Z_MID": 0.1}, {"Z_MID": 1.2}]), 1.2)

    def test_retained_source_fractions_are_per_bin(self) -> None:
        rows = [
            {"Z_MID": 0.1, "BIN1": 1.0, "BIN2": 1.0, "BIN3": 1.0, "BIN4": 1.0, "BIN5": 1.0},
            {"Z_MID": 0.2, "BIN1": 1.0, "BIN2": 1.0, "BIN3": 1.0, "BIN4": 1.0, "BIN5": 1.0},
            {"Z_MID": 0.3, "BIN1": 1.0, "BIN2": 1.0, "BIN3": 1.0, "BIN4": 1.0, "BIN5": 1.0},
        ]

        fractions = retained_source_fractions(rows, 0.2)

        self.assertEqual(sorted(fractions), ["bin1", "bin2", "bin3", "bin4", "bin5"])
        self.assertLess(fractions["bin1"], 1.0)

    def test_payload_is_diagnostic_for_requested_q0(self) -> None:
        payload = build_payload([-0.087, -0.06])

        self.assertEqual(payload["dimension"], 75)
        self.assertEqual(len(payload["rows"]), 2)
        self.assertIn("min_retained_source_fraction", payload["rows"][0])
        self.assertFalse(payload["prediction_ready"])


if __name__ == "__main__":
    unittest.main()
