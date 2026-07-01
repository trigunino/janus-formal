from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_cmb_planck_channel_isolator import CHANNELS, build_payload


class P0EFTCMBPlanckChannelIsolatorTests(unittest.TestCase):
    def test_channel_isolator_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(len(payload["channels"]), len(CHANNELS))
        self.assertGreater(payload["valid_channels"], 0)
        self.assertIsNotNone(payload["worst_channel"])
        self.assertTrue(Path(payload["csv"]).exists())

    def test_each_valid_channel_has_chi2(self) -> None:
        payload = build_payload()

        for row in payload["channels"]:
            if row["returncode"] == 0:
                self.assertIsNotNone(row["chi2"])


if __name__ == "__main__":
    unittest.main()
