from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_integrated_negative_imprint_branch import build_payload, write_reports


class P0EFTJanusZ4IntegratedNegativeImprintBranchTests(unittest.TestCase):
    def test_integrated_branch_exports_gate_ready_spectra(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-integrated-negative-imprint-branch")
        self.assertTrue(payload["branch_only_diagnostic"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertFalse(payload["observational_planck_gate_passed"])
        self.assertTrue(payload["finite_spectra_exported"])
        self.assertEqual(payload["fixed_choices"]["negative_imprint_mode"], "jeans_blue")
        self.assertTrue(payload["fixed_choices"]["no_continuous_fit_factor"])
        self.assertGreaterEqual(payload["ell_max"], 2508)
        self.assertTrue(Path(payload["spectra_path"]).exists())

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_integrated_negative_imprint_branch.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_integrated_negative_imprint_branch.md").exists())


if __name__ == "__main__":
    unittest.main()
