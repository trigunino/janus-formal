from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_post_closure_planck_decomposition import build_payload, write_reports


class P0EFTJanusZ4PostClosurePlanckDecompositionTests(unittest.TestCase):
    def test_post_closure_decomposition_keeps_planck_false(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-post-internal-closure-planck-decomposition")
        self.assertTrue(payload["physical_closure_triad_ready"])
        self.assertFalse(payload["official_planck_gate_passed"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertEqual(payload["priority_order"][0], "highl_TE")
        self.assertIn("lensing", payload["channel_decomposition"])
        self.assertEqual(payload["next_theory_correction"]["minimal_next_artifact"], "P0EFTJanusZ4AcousticPolarizationPhaseKernel")
        self.assertTrue(payload["next_theory_correction"]["artifact_scaffold_ready"])
        self.assertTrue(payload["next_theory_correction"]["tight_quadrupole_report_used"])
        self.assertTrue(payload["next_theory_correction"]["tight_coupling_identity_derived"])
        self.assertFalse(payload["phase_kernel_status"]["requires_tight_coupling_quadrupole_identity"])
        self.assertTrue(payload["next_theory_correction"]["phase_application_diagnostic_used"])
        self.assertIsInstance(payload["next_theory_correction"]["phase_application_integration_recommended"], bool)
        self.assertIsInstance(payload["next_theory_correction"]["damped_phase_application_integration_recommended"], bool)
        self.assertIsInstance(payload["next_theory_correction"]["safe_solver_integration_recommended"], bool)
        self.assertIsInstance(payload["next_theory_correction"]["parity_mixer_safe_solver_integration_recommended"], bool)
        self.assertIsInstance(payload["next_theory_correction"]["membrane_transport_safe_solver_integration_recommended"], bool)
        self.assertTrue(payload["phase_application_status"]["branch_only_diagnostic"])
        self.assertFalse(payload["phase_application_status"]["solver_numerics_modified"])
        self.assertFalse(payload["phase_application_status"]["planck_validation_claimed"])
        self.assertIsInstance(payload["phase_application_status"]["safe_solver_integration_recommended"], bool)
        self.assertIn("damped_highl_te_chi2_per_dof_delta", payload["phase_application_status"])
        self.assertTrue(payload["parity_mixer_status"]["branch_only_diagnostic"])
        self.assertFalse(payload["parity_mixer_status"]["solver_numerics_modified"])
        self.assertFalse(payload["parity_mixer_status"]["planck_validation_claimed"])
        self.assertIn("best_alpha_H", payload["parity_mixer_status"])
        self.assertTrue(payload["membrane_transport_status"]["branch_only_diagnostic"])
        self.assertFalse(payload["membrane_transport_status"]["solver_numerics_modified"])
        self.assertFalse(payload["membrane_transport_status"]["planck_validation_claimed"])
        self.assertEqual(payload["membrane_transport_status"]["a_sigma"], "2/3")
        self.assertTrue(payload["geometric_screen_status"]["branch_only_diagnostic"])
        self.assertTrue(payload["geometric_screen_status"]["no_continuous_fit_factor"])
        self.assertFalse(payload["geometric_screen_status"]["solver_numerics_modified"])
        self.assertFalse(payload["geometric_screen_status"]["planck_validation_claimed"])
        self.assertIsInstance(payload["geometric_screen_status"]["recommended_next_branches"], list)

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_post_closure_planck_decomposition.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_post_closure_planck_decomposition.md").exists())


if __name__ == "__main__":
    unittest.main()
