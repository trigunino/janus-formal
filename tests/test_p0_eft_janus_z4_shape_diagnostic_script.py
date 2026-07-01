from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_shape_diagnostic import build_payload, write_reports


class P0EFTJanusZ4ShapeDiagnosticScriptTests(unittest.TestCase):
    def test_shape_diagnostic_reports_bands(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["shape_diagnostic_ready"])
        self.assertTrue(payload["native_z4_provider_used"])
        self.assertFalse(payload["compressed_lcdm_parameters_used"])
        self.assertIn("highl_TT_damping", payload["bands"])
        self.assertIn(payload["worst_band"], payload["bands"])
        self.assertGreaterEqual(len(payload["bands"]["highl_TE"]["dominant_pulls"]), 1)

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_shape_diagnostic.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_shape_diagnostic.md").exists())
        self.assertTrue(payload["shape_diagnostic_ready"])


if __name__ == "__main__":
    unittest.main()
