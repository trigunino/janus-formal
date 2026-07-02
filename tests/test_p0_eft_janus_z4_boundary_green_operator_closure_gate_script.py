import unittest

from scripts.build_p0_eft_janus_z4_boundary_green_operator_closure_gate import build_payload


class P0EFTJanusZ4BoundaryGreenOperatorClosureGateTests(unittest.TestCase):
    def test_operator_closure_blocks_until_green_kernel_is_derived(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-boundary-green-operator-closure-gate")
        self.assertEqual(payload["green_operator_type"], "boundary_normal")
        self.assertTrue(payload["L_slip_Z4_declared"])
        self.assertTrue(payload["operator_domain_declared"])
        self.assertTrue(payload["operator_source_declared"])
        self.assertTrue(payload["boundary_conditions_declared"])
        self.assertFalse(payload["Green_solves_operator_equation"])
        self.assertFalse(payload["boundary_jump_conditions_satisfied"])
        self.assertFalse(payload["normalization_fixed"])
        self.assertEqual(payload["homogeneous_mode_policy"], "unresolved")
        self.assertFalse(payload["homogeneous_mode_removed_or_fixed"])
        self.assertTrue(payload["GR_limit_slip_zero"])
        self.assertFalse(payload["k_zero_regular"])
        self.assertFalse(payload["large_k_regular"])
        self.assertFalse(payload["free_slip_amplitude"])
        self.assertFalse(payload["free_eta_ratio"])
        self.assertFalse(payload["manual_deltaSlip_table"])
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["Planck_trial"])
        self.assertFalse(payload["deltaSlip_value_transport_available"])
        self.assertFalse(payload["operator_closure_gate_passed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
