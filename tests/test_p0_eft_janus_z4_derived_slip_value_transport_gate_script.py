import unittest

from scripts.build_p0_eft_janus_z4_derived_slip_value_transport_gate import build_payload


class P0EFTJanusZ4DerivedSlipValueTransportGateTests(unittest.TestCase):
    def test_value_transport_uses_boundary_normal_projection(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-derived-slip-value-transport-gate")
        self.assertTrue(payload["green_kernel_from_previous_gate_used"])
        self.assertEqual(payload["visible_slip_projection"], "boundary_normal_derivative")
        self.assertTrue(payload["boundary_value_zero_if_Dirichlet"])
        self.assertGreater(payload["deltaSlip_norm"], 0.0)
        self.assertGreater(payload["deltaSlipDot_norm"], 0.0)
        self.assertTrue(payload["visible_slip_nonzero"])
        self.assertTrue(payload["deltaSlip_Z4_value_available"])
        self.assertTrue(payload["deltaSlip_Z4_dot_available"])
        self.assertTrue(payload["k_zero_limit_finite"])
        self.assertTrue(payload["large_k_decay_or_bound"])
        self.assertTrue(payload["source_to_value_linearity_check"])
        self.assertTrue(payload["normalization_inherited_from_green_kernel"])
        self.assertTrue(payload["homogeneous_mode_not_reintroduced"])
        self.assertFalse(payload["free_slip_amplitude"])
        self.assertFalse(payload["free_eta_ratio"])
        self.assertFalse(payload["manual_deltaSlip_table"])
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["raw_toy_LOS"])
        self.assertFalse(payload["planck_trial_allowed"])
        self.assertTrue(payload["derived_slip_value_transport_gate_passed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
