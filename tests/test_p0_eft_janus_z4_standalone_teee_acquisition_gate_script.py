import unittest

from scripts.build_p0_eft_janus_z4_standalone_teee_acquisition_gate import build_payload


class P0EFTJanusZ4StandaloneTEEEAcquisitionGateTests(unittest.TestCase):
    def test_standalone_teee_acquisition_gate(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-standalone-teee-acquisition-gate")
        self.assertTrue(payload["robust_available_channel_candidate"])
        self.assertTrue(payload["standalone_highl_TE_available"])
        self.assertTrue(payload["standalone_highl_EE_available"])
        self.assertTrue(payload["standalone_highl_TE_EE_acquired"])
        self.assertTrue(payload["standalone_likelihood_locator"]["TE"]["wrapper_present"])
        self.assertTrue(payload["standalone_likelihood_locator"]["EE"]["wrapper_present"])
        self.assertTrue(payload["standalone_likelihood_locator"]["TE"]["clik_data_present"])
        self.assertTrue(payload["standalone_likelihood_locator"]["EE"]["clik_data_present"])
        self.assertTrue(payload["candidate_must_remain_frozen_for_next_trial"])
        self.assertTrue(payload["no_parameter_retuning"])
        self.assertTrue(payload["no_new_delta_channel"])
        self.assertTrue(payload["no_slip_opening"])
        self.assertTrue(payload["no_recombination_opening"])
        self.assertTrue(payload["no_visibility_opening"])
        self.assertTrue(payload["no_mirror_sector_opening"])
        self.assertTrue(payload["no_primordial_shape_opening"])
        self.assertTrue(payload["no_raw_native_toy_LOS"])
        self.assertFalse(payload["full_highl_decomposition_trial_allowed"])
        self.assertFalse(payload["full_planck_validation_allowed"])
        self.assertTrue(payload["standalone_teee_acquisition_gate_passed"])
        self.assertEqual(payload["candidate_spec_frozen"]["lambda_T"], -8.0e-3)
        self.assertEqual(payload["candidate_spec_frozen"]["lambda_E"], -2.0e-2)


if __name__ == "__main__":
    unittest.main()
