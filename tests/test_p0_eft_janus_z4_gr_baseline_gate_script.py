from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_gr_baseline_gate import build_payload, write_reports


class P0EFTJanusZ4GRBaselineGateTests(unittest.TestCase):
    def test_gr_baseline_is_finite_without_claiming_planck(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-gr-baseline-gate")
        self.assertFalse(payload["z4_sector_enabled"])
        self.assertFalse(payload["negative_sector_enabled"])
        self.assertFalse(payload["torsion_enabled"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertTrue(payload["visibility_normalized"])
        self.assertTrue(payload["finite_sources"])
        self.assertTrue(payload["finite_spectra"])
        self.assertTrue(payload["positive_auto_spectra"])
        self.assertTrue(payload["gr_baseline_gate_ready"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_gr_baseline_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_gr_baseline_gate.md").exists())


if __name__ == "__main__":
    unittest.main()
