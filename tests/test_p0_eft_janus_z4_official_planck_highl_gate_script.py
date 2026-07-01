from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_official_planck_highl_gate import LIKELIHOODS, build_payload, write_reports


class P0EFTJanusZ4OfficialPlanckHighLGateScriptTests(unittest.TestCase):
    def test_official_highl_planck_channels_are_attempted(self) -> None:
        payload = build_payload()

        self.assertEqual(set(payload["channels"]), set(LIKELIHOODS))
        self.assertTrue(payload["official_planck_highl_executed"])
        self.assertGreaterEqual(payload["official_planck_highl_channels_executed"], 1)
        self.assertFalse(payload["legacy_camb_fork_required"])
        self.assertFalse(payload["observational_planck_gate_passed"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_official_planck_highl_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_official_planck_highl_gate.md").exists())
        self.assertIn("native Z4 provider", payload["verdict"])


if __name__ == "__main__":
    unittest.main()
