import unittest

from scripts.run_p0_eft_janus_z4_acoustic_polarization_closed_theta2_joint_gate import (
    LAMBDA_E_GRID,
    LAMBDA_T_GRID,
    build_payload,
)


class P0EFTJanusZ4AcousticPolarizationClosedTheta2JointGateTests(unittest.TestCase):
    def test_closed_theta2_joint_scaffold(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "janus-z4-acoustic-polarization-closed-theta2-joint-gate")
        self.assertEqual(tuple(payload["lambda_T_grid"]), LAMBDA_T_GRID)
        self.assertEqual(tuple(payload["lambda_E_grid"]), LAMBDA_E_GRID)
        self.assertEqual(payload["theta2_closure_status"], "tight_coupling_derived_effective")
        self.assertFalse(payload["boltzmann_hierarchy_closed"])
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["visibility_delta_enabled"])
        self.assertFalse(payload["background_projection_changed"])
        self.assertFalse(payload["r_s_changed"])
        self.assertFalse(payload["r_d_changed"])
        self.assertFalse(payload["primordial_delta_enabled"])
        self.assertTrue(payload["lensing_C_phi_phi_frozen"])
        self.assertTrue(payload["slip_frozen"])
        self.assertFalse(payload["official_likelihood_executed"])
        self.assertFalse(payload["full_planck_verdict"])

        self.assertTrue(payload["joint_rows"])
        for row in payload["joint_rows"].values():
            diagnostics = row["diagnostics"]
            self.assertEqual(diagnostics["C_phi_phi_delta"], 0.0)
            self.assertEqual(diagnostics["visibility_delta"], 0.0)
            self.assertEqual(diagnostics["TT_change_from_lambda_E"], 0.0)
            self.assertEqual(diagnostics["EE_change_from_lambda_T"], 0.0)
            self.assertTrue(diagnostics["hard_phase_guard"])


if __name__ == "__main__":
    unittest.main()
