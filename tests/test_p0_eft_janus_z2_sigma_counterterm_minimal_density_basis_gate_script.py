import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_minimal_density_basis_gate import (
    build_payload,
)


class CountertermMinimalDensityBasisGateTests(unittest.TestCase):
    def test_minimal_basis_is_small_but_not_solvable_without_residual_constraints(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(
            payload["model_status"], "minimal_basis_diagnostic_not_active_L_ct_solution"
        )
        self.assertEqual(
            payload["minimal_basis"]["kept_terms"],
            ["linear_K", "K_squared", "intrinsic_curvature"],
        )
        self.assertEqual(payload["minimal_basis"]["basis_size"], 3)
        self.assertTrue(payload["independent_constraints_available"]["zero_reference_throat"])
        self.assertFalse(payload["independent_constraints_available"]["cancel_metric_residual_trace"])
        self.assertFalse(payload["independent_constraints_available"]["cancel_extrinsic_residual_trace"])
        self.assertFalse(payload["solvability"]["coefficient_system_solvable_now"])
        self.assertEqual(
            payload["solvability"]["primary_blocker"],
            "R_h_trace_and_R_K_trace_constraints",
        )


if __name__ == "__main__":
    unittest.main()
