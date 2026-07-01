from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_peak_damping_diagnostic import build_payload, write_reports


class P0EFTJanusZ4PeakDampingDiagnosticScriptTests(unittest.TestCase):
    def test_peak_damping_payload_exposes_phase_and_damping(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["peak_damping_diagnostic_ready"])
        self.assertTrue(payload["native_z4_provider_used"])
        self.assertFalse(payload["compressed_lcdm_parameters_used"])
        self.assertFalse(payload["official_planck_likelihood_executed"])
        self.assertFalse(payload["cmb_engine_physically_closed"])
        self.assertIn("paired_peaks", payload["tt_peak_phase"])
        self.assertIn("slope_residual", payload["tt_damping_slope"])
        self.assertIn("te_zero_crossings_found", payload)

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_peak_damping_diagnostic.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_peak_damping_diagnostic.md").exists())
        self.assertTrue(payload["peak_damping_diagnostic_ready"])


if __name__ == "__main__":
    unittest.main()
