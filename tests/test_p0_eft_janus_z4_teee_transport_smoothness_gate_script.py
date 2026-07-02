import unittest

from scripts.build_p0_eft_janus_z4_teee_transport_smoothness_gate import build_payload


class P0EFTJanusZ4TEEETransportSmoothnessGateTests(unittest.TestCase):
    def test_teee_transport_smoothness(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-teee-transport-smoothness-gate")
        self.assertEqual(payload["theta2_input_status"], "tight_coupling_derived_effective")
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["visibility_delta_enabled"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["background_projection_changed"])
        self.assertFalse(payload["r_s_changed"])
        self.assertFalse(payload["r_d_changed"])
        self.assertFalse(payload["primordial_delta_enabled"])
        self.assertTrue(payload["lensing_C_phi_phi_frozen"])
        self.assertTrue(payload["slip_frozen"])
        self.assertTrue(payload["compared_against_source_tagged_effective_theta2"])
        self.assertTrue(payload["TE_residual_smoothness_improved"])
        self.assertTrue(payload["EE_residual_smoothness_improved"])
        self.assertLess(payload["smoothness_ratios_new_over_old"]["TE_second_difference"], 0.95)
        self.assertLess(payload["smoothness_ratios_new_over_old"]["EE_second_difference"], 0.35)
        self.assertTrue(payload["TEEE_transport_smoothness_gate_passed"])


if __name__ == "__main__":
    unittest.main()
