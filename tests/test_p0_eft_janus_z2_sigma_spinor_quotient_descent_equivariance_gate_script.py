import unittest

from scripts.build_p0_eft_janus_z2_sigma_spinor_quotient_descent_equivariance_gate import (
    build_payload,
)


class SpinorQuotientDescentEquivarianceGateTests(unittest.TestCase):
    def test_quotient_descent_route_is_declared_without_promotion(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["declared"]["equivariant_bundle_descent_theorem_imported"])
        self.assertTrue(payload["declared"]["local_U_Z2_sigma_imported"])
        self.assertFalse(
            payload["physical_spinor_equivariance_from_quotient_descent_ready"]
        )
        self.assertEqual(
            payload["primary_blocker"],
            "resolved_tunnel_Pin_lift_for_spinor_descent",
        )

    def test_route_forbids_independent_sheet_spinor_shortcut(self):
        payload = build_payload()

        self.assertIn("independent plus/minus spinors without quotient descent", payload["forbidden"])
        self.assertIn("legacy Z4 monodromy", payload["forbidden"])
        self.assertIn("close_resolved_tunnel_Pin_lift_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
