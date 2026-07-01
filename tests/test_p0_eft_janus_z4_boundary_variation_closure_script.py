from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_boundary_variation_closure import build_payload, write_reports


class P0EFTJanusZ4BoundaryVariationClosureScriptTests(unittest.TestCase):
    def test_boundary_residuals_cancel_without_bimetric_geometry(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["total_boundary_residual"], "0")
        self.assertEqual(payload["single_z4_geometry_constraint"], "0")
        self.assertTrue(payload["boundary_variation_scaffold_ready"])
        self.assertFalse(payload["nonlinear_boundary_variation_closed"])
        self.assertFalse(payload["full_action_variation_closed"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_boundary_variation_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_boundary_variation_closure.md").exists())
        self.assertIn("nonlinear Z4 action", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
