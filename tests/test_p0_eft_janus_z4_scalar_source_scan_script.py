from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_scalar_source_scan import build_payload, write_reports


class P0EFTJanusZ4ScalarSourceScanScriptTests(unittest.TestCase):
    def test_scalar_source_scan_reports_lowtt_and_components(self) -> None:
        payload = build_payload(scales=(5.0, 6.0))

        self.assertTrue(payload["scalar_source_scan_ready"])
        self.assertTrue(payload["native_z4_solver_used"])
        self.assertFalse(payload["compressed_lcdm_parameters_used"])
        self.assertFalse(payload["official_planck_likelihood_executed"])
        self.assertTrue(payload["active_model_included"])
        self.assertEqual(len(payload["rows"]), 2)
        self.assertIn("mean_component_fractions", payload["rows"][0])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_scalar_source_scan.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_scalar_source_scan.md").exists())
        self.assertTrue(payload["scalar_source_scan_ready"])


if __name__ == "__main__":
    unittest.main()
