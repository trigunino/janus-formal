import unittest

from scripts.build_p0_eft_janus_z4_weyl_late_isw_consistency_gate import build_payload


class P0EFTJanusZ4WeylLateISWConsistencyGateTests(unittest.TestCase):
    def test_shared_weyl_late_isw_consistency_gate(self):
        payload = build_payload()
        consistency = payload["consistency"]

        self.assertEqual(payload["status"], "janus-z4-weyl-late-isw-consistency-gate")
        self.assertEqual(payload["delta_level"], "shared_source")
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertTrue(payload["late_ISW_delta_enabled"])
        self.assertFalse(payload["early_ISW_delta_enabled"])
        self.assertTrue(payload["recombination_source_unchanged"])
        self.assertTrue(payload["visibility_unchanged"])
        self.assertTrue(payload["acoustic_driving_unchanged"])
        self.assertTrue(payload["polarization_source_unchanged"])
        self.assertTrue(payload["lambda_zero_identity_passed"])
        self.assertTrue(consistency["weyl_potential_delta_declared"])
        self.assertTrue(consistency["weyl_delta_shared_between_lensing_and_isw"])
        self.assertFalse(consistency["independent_lensing_weyl_delta"])
        self.assertFalse(consistency["independent_isw_weyl_delta"])
        self.assertTrue(consistency["lensing_kernel_uses_X_Z4"])
        self.assertTrue(consistency["isw_source_is_time_derivative_of_weyl_delta"])
        self.assertTrue(payload["consistency_residual_passed"])
        self.assertTrue(payload["no_early_isw_leakage"])
        self.assertTrue(payload["small_lambda_continuity_passed"])
        self.assertTrue(payload["weyl_late_isw_consistency_gate_passed"])
        self.assertTrue(payload["official_planck_weyl_late_isw_trial_allowed"])


if __name__ == "__main__":
    unittest.main()
