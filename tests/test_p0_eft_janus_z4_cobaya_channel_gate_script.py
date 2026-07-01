from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_cobaya_channel_gate import build_payload, write_reports


class P0EFTJanusZ4CobayaChannelGateScriptTests(unittest.TestCase):
    def test_cobaya_channel_gate_runs_or_reports_error(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["legacy_camb_fork_required"])
        self.assertFalse(payload["official_planck_likelihood_executed"])
        if payload["cobaya_channel_gate_ready"]:
            self.assertIn("chi2_janus_z4_total", payload["chi2"])
            self.assertGreaterEqual(payload["chi2"]["chi2_janus_z4_total"], 0.0)
        else:
            self.assertIsNotNone(payload["error"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cobaya_channel_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cobaya_channel_gate.md").exists())
        self.assertIn("cobaya_channel_gate_ready", payload)


if __name__ == "__main__":
    unittest.main()
