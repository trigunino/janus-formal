from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_official_planck_lowlevel_gate import LIKELIHOODS, build_payload, write_reports


class P0EFTJanusZ4OfficialPlanckLowLevelGateScriptTests(unittest.TestCase):
    def test_official_lowlevel_planck_channels_are_attempted(self) -> None:
        payload = build_payload()

        self.assertEqual(set(payload["channels"]), set(LIKELIHOODS))
        self.assertTrue(payload["official_planck_likelihood_executed"])
        self.assertFalse(payload["legacy_camb_fork_required"])
        self.assertTrue(payload["safe_gr_baseline_provider_used"])
        self.assertFalse(payload["toy_native_source_engine_used"])
        self.assertFalse(payload["observational_planck_gate_passed"])
        self.assertGreaterEqual(payload["official_planck_channels_executed"], 1)

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_official_planck_lowlevel_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_official_planck_lowlevel_gate.md").exists())
        self.assertIn("safe GR-baseline provider", payload["verdict"])


if __name__ == "__main__":
    unittest.main()
