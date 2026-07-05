import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_normal_current_z2_cancellation_gate import (
    build_payload,
)


class DiracNormalCurrentZ2CancellationGateTests(unittest.TestCase):
    def test_z2_cancellation_route_is_declared_but_not_closed(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["declared"]["no_MIT_boundary_assumption_required_for_this_route"])
        self.assertTrue(payload["closure"]["Z2_normal_reversal_ready"])
        self.assertTrue(payload["closure"]["conditional_current_parity_algebra_ready"])
        self.assertFalse(payload["closure"]["Dirac_current_Z2_parity_derived"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["primary_blocker"],
            "spinor_equivariance_routes_open",
        )
        self.assertIn(
            "spinor_soldering_boundary_variation_residual",
            payload["route_blockers"],
        )
        self.assertIn(
            "resolved_tunnel_Pin_lift_for_spinor_descent",
            payload["route_blockers"],
        )

    def test_formula_records_required_current_parity(self):
        payload = build_payload()

        self.assertIn("J_- = sigma_J", payload["formulas"]["current_parity_needed"])
        self.assertIn("J_n^-", payload["formulas"]["normal_current_relation"])
        self.assertIn("derive_Dirac_current_Z2_parity_from_spinor_projection", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
