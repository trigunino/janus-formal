from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_lensing_amplitude_diagnostic import build_payload, write_reports


class P0EFTJanusZ4LensingAmplitudeDiagnosticScriptTests(unittest.TestCase):
    def test_lensing_amplitude_scan_executes(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["official_planck_lensing_executed"])
        self.assertTrue(payload["native_z4_spectra_used"])
        self.assertFalse(payload["compressed_lcdm_parameters_used"])
        self.assertIsNotNone(payload["best"])
        self.assertFalse(payload["amplitude_only_sufficient"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_lensing_amplitude_diagnostic.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_lensing_amplitude_diagnostic.md").exists())
        self.assertIn("rows", payload)


if __name__ == "__main__":
    unittest.main()
