import unittest

from scripts.derive_p0_eft_janus_z2_sigma_global_regular_tunnel_radius_selection_gate import (
    build_payload,
)


class JanusZ2SigmaGlobalRegularTunnelRadiusSelectionGateTest(unittest.TestCase):
    def test_declares_ratio_selection_without_fit_or_torus_replacement(self):
        payload = build_payload()
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["torus_replacement_used"])
        self.assertFalse(payload["observational_fit_used"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertIn("R_Sigma / ell_collar", payload["lambda_symbol"])
        self.assertIn("F_reg", payload["selection_equation_target"])

    def test_does_not_claim_radius_closure_before_global_functional(self):
        payload = build_payload()
        self.assertFalse(payload["radius_selection_ready"])
        self.assertFalse(payload["derived_now"]["R_Sigma_over_ell_collar_fixed"])
        self.assertEqual(
            payload["primary_blocker"],
            "F_reg_lambda_not_computed_from_active_embedding",
        )
        self.assertIn(
            "compute normal-frame holonomy around the Z2 tunnel collar",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
