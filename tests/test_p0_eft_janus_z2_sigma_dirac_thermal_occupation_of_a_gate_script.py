import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_thermal_occupation_of_a_gate import build_payload


class P0EFTJanusZ2SigmaDiracThermalOccupationOfAGateTests(unittest.TestCase):
    def test_thermal_occupation_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_thermal_occupation_ledger_declared"])
        self.assertTrue(payload["declared"]["Fermi_Dirac_occupation_declared"])
        self.assertTrue(payload["declared"]["chemical_potential_gate_declared"])
        self.assertTrue(payload["declared"]["degeneracy_factor_gate_declared"])
        self.assertIn("occupation_pm", payload["formulas"])
        self.assertTrue(payload["declared"]["observational_fit_forbidden"])

    def test_thermal_occupation_waits_for_normalization_and_temperature(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_number_normalization_ready"])
        self.assertFalse(payload["closure"]["plus_mass_temperature_law_ready"])
        self.assertFalse(payload["dirac_thermal_occupation_ready"])
        self.assertIn("pass_Dirac_number_normalization_gate", payload["next_required"])
        self.assertIn("pass_Dirac_chemical_potential_gate", payload["next_required"])
        self.assertIn("pass_Dirac_degeneracy_factor_gate", payload["next_required"])
        self.assertIn("feed_result_to_fermion_distribution_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
