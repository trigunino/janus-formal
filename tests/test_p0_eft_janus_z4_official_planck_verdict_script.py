from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_official_planck_verdict import build_payload, write_reports


class P0EFTJanusZ4OfficialPlanckVerdictScriptTests(unittest.TestCase):
    def test_official_planck_verdict_is_rejection_without_lcdm_compressed_params(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["native_z4_spectra_used"])
        self.assertFalse(payload["compressed_lcdm_parameters_used"])
        self.assertFalse(payload["legacy_camb_fork_required"])
        self.assertTrue(payload["official_planck_likelihood_executed"])
        self.assertFalse(payload["observational_planck_gate_passed"])
        self.assertTrue(payload["finite_channel_chi2"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_official_planck_verdict.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_official_planck_verdict.md").exists())
        self.assertIn("Rejected", payload["verdict"])


if __name__ == "__main__":
    unittest.main()
