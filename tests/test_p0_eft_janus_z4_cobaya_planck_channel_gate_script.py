from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_cobaya_planck_channel_gate import CHANNELS, build_payload, write_reports


class P0EFTJanusZ4CobayaPlanckChannelGateScriptTests(unittest.TestCase):
    def test_planck_like_channels_are_decomposed_without_official_claim(self) -> None:
        payload = build_payload()

        self.assertEqual(set(payload["channels"]), set(CHANNELS))
        self.assertTrue(payload["channel_gate_ready"])
        self.assertTrue(payload["native_z4_provider_used"])
        self.assertFalse(payload["legacy_camb_fork_required"])
        self.assertFalse(payload["official_planck_likelihood_executed"])
        self.assertFalse(payload["observational_planck_gate_passed"])
        self.assertIn(payload["worst_channel"], CHANNELS)

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cobaya_planck_channel_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cobaya_planck_channel_gate.md").exists())
        self.assertIn("Planck-like", payload["note"])


if __name__ == "__main__":
    unittest.main()
