import unittest

from scripts.run_p0_eft_janus_z4_acoustic_polarization_joint_consistency_gate import (
    LAMBDA_E_GRID,
    LAMBDA_T_GRID,
    build_payload,
)


class P0EFTJanusZ4AcousticPolarizationJointConsistencyGateTests(unittest.TestCase):
    def test_joint_consistency_scaffold(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "janus-z4-acoustic-polarization-joint-consistency-gate")
        self.assertEqual(tuple(payload["lambda_T_grid"]), LAMBDA_T_GRID)
        self.assertEqual(tuple(payload["lambda_E_grid"]), LAMBDA_E_GRID)
        self.assertEqual(payload["temperature_component"], "early_isw_only")
        self.assertEqual(payload["polarization_component"], "Theta2_quadrupole_response")
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
        self.assertTrue(payload["available_planck_channels_only"])
        self.assertTrue(payload["missing_highl_TE_EE_standalone_clik"])
        self.assertFalse(payload["official_likelihood_requested"])
        self.assertFalse(payload["official_likelihood_executed"])
        self.assertIn("hard_phase_guard_passed", payload)

        self.assertTrue(payload["joint_rows"])
        for row in payload["joint_rows"].values():
            diagnostics = row["diagnostics"]
            self.assertEqual(diagnostics["TT_change_from_lambda_E"], 0.0)
            self.assertEqual(diagnostics["EE_change_from_lambda_T"], 0.0)
            self.assertEqual(diagnostics["C_phi_phi_delta"], 0.0)
            self.assertEqual(diagnostics["visibility_delta"], 0.0)


if __name__ == "__main__":
    unittest.main()
