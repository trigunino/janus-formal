import unittest

from scripts.build_p0_eft_janus_z4_boundary_normal_green_kernel_solution_gate import build_payload


class P0EFTJanusZ4BoundaryNormalGreenKernelSolutionGateTests(unittest.TestCase):
    def test_boundary_normal_green_kernel_solution_passes_without_planck(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-boundary-normal-green-kernel-solution-gate")
        self.assertTrue(payload["green_equation_solved"])
        self.assertTrue(payload["boundary_jump_conditions_satisfied"])
        self.assertTrue(payload["normalization_fixed"])
        self.assertEqual(payload["homogeneous_mode_policy"], "removed_by_Z4_Dirichlet_boundaries")
        self.assertTrue(payload["homogeneous_mode_removed"])
        self.assertTrue(payload["k_zero_regular"])
        self.assertTrue(payload["large_k_regular"])
        self.assertTrue(payload["GR_limit_slip_zero"])
        self.assertFalse(payload["free_slip_parameter"])
        self.assertFalse(payload["free_eta_ratio"])
        self.assertFalse(payload["manual_deltaSlip_table"])
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["raw_toy_LOS"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertTrue(payload["green_kernel_derived"])
        self.assertTrue(payload["deltaSlip_value_transport_available"])
        self.assertTrue(payload["deltaSlipDot_Z4_available"])
        self.assertTrue(payload["source_level_slip_regeneration_possible"])
        self.assertTrue(payload["boundary_normal_green_kernel_solution_gate_passed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
