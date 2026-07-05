import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_torsion_pullback_variation_transport_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackVariationTransportGateTests(unittest.TestCase):
    def test_cartan_tetrad_variation_formula_is_recorded(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["tetrad_torsion_pullback_variation_ledger_declared"])
        self.assertEqual(payload["formulae"]["delta_torsion"], "delta_e T^I = D_omega(delta e^I)")
        self.assertIn("delta_e_to_delta_torsion_formula_proved", payload["closed"])

    def test_pullback_transport_closes_from_symbolic_torsion_payload(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["torsion_pullback_ready"])
        self.assertTrue(payload["closure"]["pullback_commutation_ready"])
        self.assertFalse(payload["upstream_frontiers"]["torsion_pullback_on_sigma"]["ready"])
        self.assertTrue(payload["upstream_frontiers"]["oriented_pullback_commutation"]["ready"])
        self.assertTrue(payload["closure"]["symbolic_gaussian_collar_torsion_pullback_ready"])
        self.assertTrue(payload["closure"]["torsion_pullback_variation_in_allowed_basis"])
        self.assertTrue(payload["tetrad_torsion_pullback_variation_ready"])
        self.assertIn("derive_residual_coefficients_R_T_A", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
