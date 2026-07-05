import unittest

from scripts.build_p0_eft_janus_z2_sigma_perfect_fluid_tangential_flux_zero_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaPerfectFluidTangentialFluxZeroGateTests(unittest.TestCase):
    def test_perfect_fluid_flux_zero_identity_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["declared"]["perfect_fluid_flux_identity_declared"])
        self.assertTrue(payload["declared"]["rho_pressure_values_not_required_for_zero_identity"])
        self.assertEqual(payload["scope"]["Holst_torsion_flux"], "not_closed_by_this_gate")

    def test_identity_uses_orthogonality_not_negative_density(self):
        payload = build_payload()

        self.assertIn("(rho+p)(u.e_a)(u.n)+p(e_a.n)", payload["formulas"]["normal_tangent_flux"])
        self.assertEqual(payload["formulas"]["orthogonality"], "e_a.n = 0")
        self.assertEqual(payload["formulas"]["comoving_tangency"], "u.n = 0")
        self.assertEqual(payload["scope"]["Holst_torsion_flux"], "not_closed_by_this_gate")

    def test_next_required_keeps_holst_separate(self):
        payload = build_payload()

        self.assertIn("derive_plus_minus_four_velocity_tangent_to_Sigma", payload["next_required"])
        self.assertIn("handle_Holst_torsion_flux_separately", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
