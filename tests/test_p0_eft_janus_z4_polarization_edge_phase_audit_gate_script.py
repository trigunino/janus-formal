import unittest

from scripts.run_p0_eft_janus_z4_polarization_edge_phase_audit_gate import (
    EXTENDED_LAMBDA_E_GRID,
    build_payload,
)


class P0EFTJanusZ4PolarizationEdgePhaseAuditGateTests(unittest.TestCase):
    def test_edge_phase_audit_scaffold(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "janus-z4-polarization-edge-phase-audit-gate")
        self.assertEqual(tuple(payload["extended_lambda_E_grid"]), EXTENDED_LAMBDA_E_GRID)
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["visibility_delta_enabled"])
        self.assertFalse(payload["background_projection_changed"])
        self.assertFalse(payload["primordial_delta_enabled"])
        self.assertFalse(payload["lensing_delta_enabled"])
        self.assertEqual(payload["deltaSlip_Z4"], "explicit_zero_until_derived")
        self.assertTrue(payload["available_planck_channels_only"])
        self.assertTrue(payload["missing_highl_TE_EE_standalone_clik"])
        self.assertFalse(payload["official_likelihood_requested"])
        self.assertFalse(payload["official_likelihood_executed"])
        for result in payload["subchannel_results"].values():
            self.assertEqual(len(result["spectra_paths"]), len(EXTENDED_LAMBDA_E_GRID))
            self.assertTrue(result["TT_invariant_under_lambda_E"])
            self.assertTrue(result["C_phi_phi_invariant_under_lambda_E"])
            self.assertIn("full_extended_scan_perturbative_validity_passed", result)
            self.assertIn("TE_EE_phase_guard_passed_at_best", result)


if __name__ == "__main__":
    unittest.main()
