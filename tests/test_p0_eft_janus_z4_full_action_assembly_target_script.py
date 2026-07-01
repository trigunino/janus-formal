from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_full_action_assembly_target import build_payload, write_reports


class P0EFTJanusZ4FullActionAssemblyTargetScriptTests(unittest.TestCase):
    def test_full_action_assembly_keeps_nonlinear_residual_explicit(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["full_action_assembly_scaffold_ready"])
        self.assertTrue(payload["z4_rank_one_source_recovered"])
        self.assertFalse(payload["nonlinear_euler_lagrange_residual_vanishing"])
        self.assertFalse(payload["full_action_variation_closed"])
        self.assertIn("R_nl_plus", payload["nonlinear_residual"])
        self.assertIn("R_nl_minus", payload["nonlinear_residual"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_full_action_assembly_target.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_full_action_assembly_target.md").exists())
        self.assertIn("nonlinear", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
