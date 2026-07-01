from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_visibility_nonproxy_closure import build_payload, write_reports


class P0EFTJanusZ4VisibilityNonProxyClosureScriptTests(unittest.TestCase):
    def test_visibility_integrates_to_unit_weight(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["visibility_integral"], "1")
        self.assertEqual(payload["normalization_residual"], "0")
        self.assertTrue(payload["optical_depth_monotone"])
        self.assertTrue(payload["recombination_coefficients_positive"])
        self.assertTrue(payload["physical_recombination_visibility_nonproxy"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_visibility_nonproxy_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_visibility_nonproxy_closure.md").exists())
        self.assertIn("bounded ionization", payload["scope"])


if __name__ == "__main__":
    unittest.main()
