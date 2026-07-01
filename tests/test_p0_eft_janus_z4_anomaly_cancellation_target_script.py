from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_anomaly_cancellation_target import build_payload, write_reports


class P0EFTJanusZ4AnomalyCancellationTargetScriptTests(unittest.TestCase):
    def test_anomaly_channels_cancel_but_current_lock_remains(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["a_boundary"], "-A_bulk")
        self.assertEqual(payload["residual_after_measure"], "0")
        self.assertEqual(payload["obstruction_after_anomaly"], "div_J_Z4")
        self.assertEqual(payload["obstruction_if_current_conserved"], "0")
        self.assertTrue(payload["anomaly_cancellation_target_ready"])
        self.assertFalse(payload["nonlinear_current_conservation_derived"])
        self.assertFalse(payload["full_action_variation_closed"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_anomaly_cancellation_target.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_anomaly_cancellation_target.md").exists())
        self.assertIn("nonlinear Z4 gauge current", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
