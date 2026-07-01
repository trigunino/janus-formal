from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_determinant_measure_variation import build_payload, write_reports


class P0EFTJanusZ4DeterminantMeasureVariationScriptTests(unittest.TestCase):
    def test_reciprocal_determinant_variation_is_consistent(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["reciprocal_residual"], "0")
        self.assertTrue(payload["measure_variation_scaffold_ready"])
        self.assertFalse(payload["measure_variation_physical_ready"])
        self.assertIn("tr_minus", payload["delta_log_B"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_determinant_measure_variation.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_determinant_measure_variation.md").exists())
        self.assertIn("full nonlinear", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
