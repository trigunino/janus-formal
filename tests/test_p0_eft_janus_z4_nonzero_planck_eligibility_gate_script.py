import unittest

from scripts.build_p0_eft_janus_z4_nonzero_planck_eligibility_gate import build_payload


class P0EFTJanusZ4NonzeroPlanckEligibilityGateTests(unittest.TestCase):
    def test_nonzero_planck_eligibility_gate(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-nonzero-planck-eligibility-gate")
        self.assertEqual(payload["backend"], "camb_gr_plus_z4_delta")
        self.assertEqual(payload["z4_model_status"], "effective_lensing_shape_trial")
        self.assertFalse(payload["full_native_z4_solver_used"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertTrue(payload["native_toy_los_planck_forbidden"])
        self.assertTrue(payload["camb_gr_safe_baseline_roundtrip_passed"])
        self.assertTrue(payload["controlled_z4_delta_gate_passed"])
        self.assertEqual(payload["previous_weyl_delta_classification"], "near_uniform_lensing_amplitude_response")
        self.assertTrue(payload["lensing_shape_delta_gate_passed"])
        self.assertTrue(payload["lambda_zero_identity_passed"])
        self.assertTrue(payload["small_lambda_continuity_passed"])
        self.assertTrue(payload["shape_smoothness_passed"])
        self.assertTrue(payload["forbidden_channels_off"])
        self.assertEqual(payload["phiphi_convention"], "C_L_phiphi")
        self.assertTrue(payload["not_C_L_dd"])
        self.assertTrue(payload["not_L4_C_L_phiphi"])
        self.assertFalse(payload["z4_planck_passed"])
        self.assertTrue(payload["nonzero_z4_official_likelihood_allowed"])
        self.assertEqual(payload["first_allowed_planck_run_name"], "official_planck_lensing_shape_delta_trial")


if __name__ == "__main__":
    unittest.main()
