import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_mass_term_from_action_gate import build_payload


class P0EFTJanusZ2SigmaDiracMassTermFromActionGateTests(unittest.TestCase):
    def test_mass_term_from_action_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_mass_term_from_action_ledger_declared"])
        self.assertTrue(payload["declared"]["mass_bilinear_declared"])
        self.assertTrue(payload["declared"]["Z2Sigma_projected_mass_coefficient_declared"])
        self.assertIn("mass_bilinear", payload["formulas"])

    def test_mass_term_from_action_closure_remains_blocked(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_mass_coefficient_from_action_derived"])
        self.assertFalse(payload["closure"]["projected_mass_coefficient_derived"])
        self.assertFalse(payload["dirac_mass_term_from_action_ready"])
        self.assertIn("pass_plus_minus_Dirac_action_local_reduction_gate", payload["next_required"])
        self.assertIn("feed_result_to_Dirac_scalar_mass_law_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
