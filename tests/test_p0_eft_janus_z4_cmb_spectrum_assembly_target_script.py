from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_cmb_spectrum_assembly_target import build_payload, write_reports


class P0EFTJanusZ4CMBSpectrumAssemblyTargetScriptTests(unittest.TestCase):
    def test_spectra_are_finite_exportable_proxies(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["ell_grid_strictly_increasing"])
        self.assertTrue(payload["spectra_finite"])
        self.assertTrue(payload["positive_auto_spectra"])
        self.assertTrue(payload["spectra_finite_and_exportable"])
        self.assertFalse(payload["physical_transfer_functions_used"])
        self.assertFalse(payload["planck_likelihood_adapter_ready"])
        self.assertGreater(payload["row_count"], 10)

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cmb_spectrum_assembly_target.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cmb_spectrum_assembly_target.md").exists())
        self.assertTrue(Path(payload["spectra_path"]).exists())
        self.assertIn("Planck likelihood", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
