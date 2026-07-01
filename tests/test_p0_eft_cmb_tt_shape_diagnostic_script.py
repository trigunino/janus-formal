from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_cmb_tt_shape_diagnostic import build_payload


class P0EFTCMBTTShapeDiagnosticTests(unittest.TestCase):
    def test_tt_shape_diagnostic_runs(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["fork_loaded"])
        self.assertTrue(Path(payload["csv"]).exists())
        self.assertIn("peak1_shift", payload["peaks"])

    def test_band_ratios_are_positive(self) -> None:
        payload = build_payload()

        for value in payload["band_ratios"].values():
            self.assertGreater(value, 0.0)


if __name__ == "__main__":
    unittest.main()
