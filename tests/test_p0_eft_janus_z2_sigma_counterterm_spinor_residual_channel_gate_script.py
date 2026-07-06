import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_spinor_residual_channel_gate import build_payload


class P0EFTJanusZ2SigmaCountertermSpinorResidualChannelGateTests(unittest.TestCase):
    def test_spinor_channel_ledger_is_declared_without_fit(self):
        payload = build_payload()

        self.assertTrue(payload["counterterm_spinor_residual_channel_ledger_declared"])
        self.assertTrue(payload["declared"]["projected_spinor_variation_transport_declared"])
        self.assertIn("fit spinor residual coefficient", payload["forbidden"])
        self.assertIn("conditional_reflecting_projector_route", payload)

    def test_spinor_channel_closes_locally_with_projected_zero_coefficients(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["spinor_residual_coefficient_explicit"])
        self.assertTrue(payload["closure"]["conjugate_spinor_residual_coefficient_explicit"])
        self.assertTrue(payload["closure"]["spinor_residual_compatible_with_projection"])
        self.assertTrue(payload["counterterm_spinor_residual_channel_ready"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(payload["projected_residual_coefficients"]["R_psi"], "0")
        self.assertFalse(
            payload["projected_residual_coefficients"][
                "global_resolved_tunnel_spinor_bundle_claimed"
            ]
        )

    def test_reflecting_projector_route_is_conditional_only(self):
        payload = build_payload()
        route = payload["conditional_reflecting_projector_route"]

        self.assertTrue(route["local_MIT_reflecting_projector_ready"])
        self.assertTrue(route["normal_current_zero_algebra_ready"])
        self.assertTrue(route["spinor_residual_zero_if_reflecting_projector_imposed"])
        self.assertTrue(route["boundary_spinor_satisfies_projector_derived"])
        self.assertFalse(route["conditional_only_not_physical_boundary_condition"])
        self.assertFalse(route["global_Z2Sigma_spinor_projection_ready"])
        self.assertTrue(route["local_projected_spinor_residual_zero_ready"])


if __name__ == "__main__":
    unittest.main()
