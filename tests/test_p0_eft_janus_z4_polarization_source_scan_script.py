from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_polarization_source_scan import build_payload, write_reports


class P0EFTJanusZ4PolarizationSourceScanScriptTests(unittest.TestCase):
    def test_scan_compares_shear_and_quadrupole_sources(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["polarization_source_scan_ready"])
        self.assertFalse(payload["official_planck_likelihood_executed"])
        self.assertEqual(payload["active_solver_model"], "shear")
        self.assertIn("shear", {row["model"] for row in payload["rows"]})
        self.assertIn("quadrupole", {row["model"] for row in payload["rows"]})
        self.assertIn("hybrid", {row["model"] for row in payload["rows"]})
        self.assertIn(payload["best_te_phase_model"], {"shear", "quadrupole", "hybrid"})
        self.assertIn(payload["best_shape_model"], {"shear", "quadrupole", "hybrid"})
        self.assertIn("best_nontrivial_phase_model", payload)

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_polarization_source_scan.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_polarization_source_scan.md").exists())
        self.assertTrue(payload["quadrupole_kept_as_candidate"])


if __name__ == "__main__":
    unittest.main()
