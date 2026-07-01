from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_visibility_normalization_closure import build_payload, write_reports


class P0EFTJanusZ4VisibilityNormalizationClosureScriptTests(unittest.TestCase):
    def test_visibility_kernel_is_normalized_but_not_physical_solution(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["normalization_residual"], "0")
        self.assertTrue(payload["visibility_normalization_ready"])
        self.assertTrue(payload["z4_background_rate_inserted"])
        self.assertFalse(payload["ionization_history_solved"])
        self.assertFalse(payload["physical_recombination_visibility_nonproxy"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_visibility_normalization_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_visibility_normalization_closure.md").exists())
        self.assertIn("x_e(a)", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
