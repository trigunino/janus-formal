from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_gr_baseline_reduction_gate import build_payload, write_reports


class P0EFTJanusZ4GRBaselineReductionGateTests(unittest.TestCase):
    def test_camb_gr_baseline_reduces_dominant_tt_te_mismatch(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-gr-baseline-reduction-gate")
        self.assertFalse(payload["z4_sector_enabled"])
        self.assertFalse(payload["negative_sector_enabled"])
        self.assertFalse(payload["torsion_enabled"])
        self.assertTrue(payload["dominant_tt_te_mismatch_reduced"])
        self.assertTrue(payload["safe_gr_baseline_available"])
        self.assertFalse(payload["native_toy_source_engine_repaired"])
        self.assertLess(payload["reductions"]["high_tt"]["after_chi2_per_dof"], 1.0e-8)
        self.assertLess(payload["reductions"]["high_te"]["after_chi2_per_dof"], 1.0e-8)

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_gr_baseline_reduction_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_gr_baseline_reduction_gate.md").exists())


if __name__ == "__main__":
    unittest.main()
