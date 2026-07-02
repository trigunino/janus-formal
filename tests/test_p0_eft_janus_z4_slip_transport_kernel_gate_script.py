import unittest

from scripts.build_p0_eft_janus_z4_slip_transport_kernel_gate import build_payload


class P0EFTJanusZ4SlipTransportKernelGateTests(unittest.TestCase):
    def test_transport_kernel_blocks_until_green_or_normal_mode_is_derived(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-slip-transport-kernel-gate")
        self.assertTrue(payload["slip_source_equation_available"])
        self.assertFalse(payload["boundary_green_kernel_derived"])
        self.assertFalse(payload["normal_mode_transport_derived"])
        self.assertFalse(payload["slip_value_transport_available"])
        self.assertFalse(payload["deltaSlip_Z4_value_available"])
        self.assertFalse(payload["source_level_regeneration_possible"])
        self.assertFalse(payload["free_slip_parameter"])
        self.assertFalse(payload["free_eta_ratio"])
        self.assertTrue(payload["boundary_conditions_declared"])
        self.assertTrue(payload["GR_limit_slip_zero"])
        self.assertTrue(payload["Bianchi_residual_checked"])
        self.assertTrue(payload["no_direct_Cl_patch"])
        self.assertTrue(payload["raw_toy_LOS_forbidden"])
        self.assertTrue(payload["planck_trial_forbidden"])
        self.assertFalse(payload["transport_kernel_gate_passed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
