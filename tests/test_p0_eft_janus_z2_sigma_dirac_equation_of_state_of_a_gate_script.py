import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_equation_of_state_of_a_gate import build_payload


class P0EFTJanusZ2SigmaDiracEquationOfStateOfAGateTests(unittest.TestCase):
    def test_dirac_equation_of_state_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_equation_of_state_ledger_declared"])
        self.assertTrue(payload["declared"]["Fermi_Dirac_energy_pressure_integrals_imported"])
        self.assertIn("rho_pm", payload["formulas"])
        self.assertTrue(payload["declared"]["observational_fit_forbidden"])

    def test_dirac_equation_of_state_waits_for_distribution_and_regime(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_distribution_of_a_ready"])
        self.assertFalse(payload["closure"]["plus_regime_selected"])
        self.assertFalse(payload["dirac_equation_of_state_ready"])
        self.assertIn("pass_fermion_distribution_of_a_gate", payload["next_required"])
        self.assertIn("pass_Dirac_regime_selection_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
