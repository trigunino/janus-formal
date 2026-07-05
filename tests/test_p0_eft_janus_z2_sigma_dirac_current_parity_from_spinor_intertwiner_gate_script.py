import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_current_parity_from_spinor_intertwiner_gate import (
    build_payload,
)


class DiracCurrentParityFromSpinorIntertwinerGateTests(unittest.TestCase):
    def test_conditional_algebra_is_ready_but_global_parity_is_not(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["conditional_current_parity_algebra_ready"])
        self.assertTrue(payload["closure"]["local_Z2_spinor_intertwiner_on_Sigma_ready"])
        self.assertTrue(payload["closure"]["Clifford_intertwining_verified"])
        self.assertTrue(payload["closure"]["Dirac_adjoint_compatibility_verified"])
        self.assertFalse(payload["dirac_current_z2_parity_ready"])
        self.assertEqual(
            payload["primary_blocker"],
            "spinor_equivariance_routes_open",
        )
        self.assertFalse(
            payload["closure"]["physical_spinor_equivariance_from_boundary_variation_ready"]
        )
        self.assertFalse(
            payload["closure"]["physical_spinor_equivariance_from_quotient_descent_ready"]
        )
        self.assertIn(
            "resolved_tunnel_Pin_lift_for_spinor_descent",
            payload["equivariance_route_blockers"],
        )

    def test_formula_requires_clifford_and_adjoint_compatibility(self):
        payload = build_payload()

        self.assertIn("U_Z2", payload["formulas"]["spinor_intertwiner"])
        self.assertIn("gamma", payload["formulas"]["clifford_intertwining"])
        self.assertIn("psibar", payload["formulas"]["adjoint_compatibility"])
        self.assertIn(
            "close_spinor_soldering_boundary_variation_residual",
            payload["next_required"],
        )
        self.assertIn(
            "or_close_spinor_quotient_descent_equivariance",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
