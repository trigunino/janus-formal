from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_phase_kernel_application_diagnostic import build_payload, write_reports


class P0EFTJanusZ4PhaseKernelApplicationDiagnosticTests(unittest.TestCase):
    def test_branch_diagnostic_keeps_solver_and_planck_false(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-phase-kernel-application-diagnostic")
        self.assertTrue(payload["branch_only_diagnostic"])
        self.assertEqual(payload["applied_identity"], "Theta2 = k*vb/tau_dot")
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertFalse(payload["observational_planck_gate_passed"])
        self.assertIsInstance(payload["integration_recommended"], bool)
        self.assertIsInstance(payload["damped_integration_recommended"], bool)
        self.assertIsInstance(payload["safe_solver_integration_recommended"], bool)
        self.assertIn("te_zero_crossings", payload["baseline"])
        self.assertIn("te_zero_crossings", payload["tight_quadrupole"])
        self.assertIn("te_zero_crossings", payload["tight_visibility_silk"])
        self.assertIn("highl_te_chi2_per_dof_delta", payload["deltas"])
        self.assertIn("tt_peak_shift_improved", payload["deltas"])
        self.assertIn("damped_highl_te_chi2_per_dof_delta", payload["deltas"])
        self.assertIn("damped_highl_ee_chi2_per_dof_delta", payload["deltas"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_phase_kernel_application_diagnostic.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_phase_kernel_application_diagnostic.md").exists())


if __name__ == "__main__":
    unittest.main()
