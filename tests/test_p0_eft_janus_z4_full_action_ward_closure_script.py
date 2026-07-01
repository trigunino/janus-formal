from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_full_action_ward_closure import build_payload, write_reports


class P0EFTJanusZ4FullActionWardClosureScriptTests(unittest.TestCase):
    def test_current_and_anomaly_close_obstruction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["weighted_current_divergence"], "0")
        self.assertEqual(payload["anomaly_after_channel_cancellation"], "0")
        self.assertEqual(payload["obstruction"], "0")
        self.assertTrue(payload["current_conservation_ready"])
        self.assertTrue(payload["anomaly_cancellation_ready"])
        self.assertTrue(payload["full_action_variation_closed"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_full_action_ward_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_full_action_ward_closure.md").exists())
        self.assertIn("non-proxy CMB", payload["scope"])


if __name__ == "__main__":
    unittest.main()
