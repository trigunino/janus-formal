import unittest

from scripts.build_p0_eft_janus_z2_sigma_stress_equivariance_gate import build_payload


class P0EFTJanusZ2SigmaStressEquivarianceGateTests(unittest.TestCase):
    def test_stress_equivariance_is_declared_but_not_assumed(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["stress_equivariance_ledger_declared"])
        self.assertFalse(payload["stress_equivariance_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "plus_rho_p_of_a_ready")

    def test_sign_policy_does_not_set_negative_density_by_hand(self):
        payload = build_payload()

        self.assertTrue(payload["declared"]["thermodynamic_density_not_signed_by_hand"])
        self.assertTrue(payload["declared"]["gravitational_Z2_sign_policy_declared"])
        self.assertIn("rho_- is not set negative by hand", payload["formulas"]["sign_policy"])

    def test_total_stress_equivariance_requires_matter_and_holst_routes(self):
        payload = build_payload()
        closure = payload["closure"]

        self.assertFalse(closure["matter_stress_Z2_equivariance_derived"])
        self.assertFalse(closure["Holst_torsion_stress_Z2_equivariance_derived"])
        self.assertFalse(closure["total_stress_Z2_equivariance_derived"])
        self.assertIn("derive_Holst_torsion_stress_Z2_equivariance", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
