from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_planck_spectrum_export_gate import build_payload, write_reports


class P0EFTJanusZ4PlanckSpectrumExportGateScriptTests(unittest.TestCase):
    def test_spectrum_export_contract_is_valid_without_likelihood_execution(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["required_columns_present"])
        self.assertTrue(payload["ell_grid_strictly_increasing"])
        self.assertTrue(payload["spectra_finite"])
        self.assertTrue(payload["spectrum_export_gate_ready"])
        self.assertFalse(payload["planck_likelihood_executed"])
        self.assertFalse(payload["planck_likelihood_adapter_ready"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_planck_spectrum_export_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_planck_spectrum_export_gate.md").exists())
        self.assertTrue(Path(payload["spectra_path"]).exists())
        self.assertIn("direct Planck likelihood", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
