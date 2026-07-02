import unittest

from scripts.build_p0_eft_janus_z4_boundary_green_slip_transport_gate import build_payload


class P0EFTJanusZ4BoundaryGreenSlipTransportGateTests(unittest.TestCase):
    def test_boundary_green_route_blocks_until_kernel_is_derived(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-boundary-green-slip-transport-gate")
        self.assertEqual(payload["slip_transport_route"], "boundary_green")
        self.assertTrue(payload["slip_source_equation_available"])
        self.assertTrue(payload["green_kernel_declared"])
        self.assertFalse(payload["green_kernel_derived"])
        self.assertFalse(payload["retarded_causal_support"])
        self.assertTrue(payload["boundary_conditions_declared"])
        self.assertFalse(payload["normalization_fixed"])
        self.assertTrue(payload["GR_limit_slip_zero"])
        self.assertFalse(payload["no_arbitrary_homogeneous_mode"])
        self.assertFalse(payload["regular_k_to_zero"])
        self.assertFalse(payload["regular_large_k"])
        self.assertFalse(payload["slip_value_transport_available"])
        self.assertFalse(payload["deltaSlip_Z4_value_available"])
        self.assertFalse(payload["source_level_slip_regeneration_possible"])
        self.assertFalse(payload["free_slip_parameter"])
        self.assertFalse(payload["free_eta_ratio"])
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["raw_toy_LOS"])
        self.assertFalse(payload["lambda_retuning"])
        self.assertFalse(payload["planck_trial_allowed"])
        self.assertFalse(payload["boundary_green_slip_transport_gate_passed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
