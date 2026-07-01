from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_linearized_action_variation import build_payload, write_reports


class P0EFTJanusZ4LinearizedActionVariationScriptTests(unittest.TestCase):
    def test_linearized_action_variation_recovers_rank_one_source(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["residual"], "Matrix([[0], [0]])")
        self.assertTrue(payload["linearized_action_variation_ready"])
        self.assertFalse(payload["full_action_variation_ready"])
        self.assertIn("h_plus", payload["source_action_density"])
        self.assertIn("h_minus", payload["source_action_density"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_linearized_action_variation.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_linearized_action_variation.md").exists())
        self.assertIn("nonlinear", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
