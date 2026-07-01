from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_camb_gr_baseline_export import build_payload, write_reports


class P0EFTJanusZ4CAMBGRBaselineExportTests(unittest.TestCase):
    def test_camb_gr_baseline_exports_native_schema(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-camb-gr-baseline-export")
        self.assertEqual(payload["backend"], "CAMB")
        self.assertFalse(payload["z4_sector_enabled"])
        self.assertFalse(payload["negative_sector_enabled"])
        self.assertFalse(payload["torsion_enabled"])
        self.assertEqual(payload["native_schema_fields"], ["ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"])
        self.assertTrue(payload["gr_baseline_export_ready"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_camb_gr_baseline_export.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_camb_gr_baseline_export.md").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_camb_gr_baseline_spectra.csv").exists())


if __name__ == "__main__":
    unittest.main()
