from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_weyl_tt_transport_solver_branch import build_payload, write_reports


class P0EFTJanusZ4WeylTTTransportSolverBranchTests(unittest.TestCase):
    def test_branch_exports_finite_spectra(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-weyl-tt-transport-solver-branch")
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertTrue(payload["finite_spectra_exported"])
        self.assertIn("lensing", payload["deltas_vs_integrated_negative_imprint_branch"])
        self.assertTrue(Path(payload["spectra_path"]).exists())

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_weyl_tt_transport_solver_branch.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_weyl_tt_transport_solver_branch.md").exists())


if __name__ == "__main__":
    unittest.main()
