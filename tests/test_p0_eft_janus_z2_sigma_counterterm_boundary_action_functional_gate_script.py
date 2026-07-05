import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_boundary_action_functional_gate import (
    build_payload,
)


class CountertermBoundaryActionFunctionalGateTests(unittest.TestCase):
    def test_closes_symbolic_boundary_action_not_density_inputs(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["boundary_action_functional_closed"])
        self.assertTrue(payload["closure"]["induced_measure_fixed"])
        self.assertTrue(payload["closure"]["not_duplicate_proven_by_variational_role"])
        self.assertTrue(payload["closure"]["reduced_to_local_density_basis"])
        self.assertTrue(payload["closure"]["integration_constant_fixed_symbolically"])
        self.assertFalse(payload["closure"]["explicit_coefficient_expansion_ready"])
        self.assertFalse(payload["counterterm_local_density_action_inputs_allowed"])
        self.assertIn("sqrt_abs_h", payload["boundary_action"]["formula"])
        self.assertIn("compute_R_h_ab_R_K_ab_R_chi_from_S_ct_variation", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
