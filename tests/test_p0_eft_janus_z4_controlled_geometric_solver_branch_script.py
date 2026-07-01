from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_controlled_geometric_solver_branch import build_payload, write_reports


class P0EFTJanusZ4ControlledGeometricSolverBranchTests(unittest.TestCase):
    def test_branch_is_fixed_geometry_and_exports_spectra(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-controlled-geometric-solver-branch")
        self.assertTrue(payload["branch_only_diagnostic"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertFalse(payload["observational_planck_gate_passed"])
        self.assertTrue(payload["fixed_geometric_choices"]["no_continuous_fit_factor"])
        self.assertEqual(payload["fixed_geometric_choices"]["z4_quarter_turn"], "pi/2")
        self.assertIn("highl_TE", payload["shape_chi2_per_dof_deltas"])
        self.assertIn("lensing", payload["shape_chi2_per_dof_deltas"])
        self.assertTrue(Path(payload["spectra_path"]).exists())

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_controlled_geometric_solver_branch.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_controlled_geometric_solver_branch.md").exists())


if __name__ == "__main__":
    unittest.main()
