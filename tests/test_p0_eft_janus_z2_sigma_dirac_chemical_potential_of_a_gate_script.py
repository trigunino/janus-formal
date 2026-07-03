import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_chemical_potential_of_a_gate import build_payload


class P0EFTJanusZ2SigmaDiracChemicalPotentialOfAGateTests(unittest.TestCase):
    def test_chemical_potential_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_chemical_potential_ledger_declared"])
        self.assertTrue(payload["declared"]["number_constraint_equation_declared"])
        self.assertTrue(payload["declared"]["no_chemical_potential_fit"])
        self.assertIn("chemical_potential_solution", payload["formulas"])

    def test_chemical_potential_waits_for_number_temperature_and_regime(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_number_normalization_ready"])
        self.assertFalse(payload["closure"]["plus_chemical_potential_solved"])
        self.assertFalse(payload["dirac_chemical_potential_ready"])
        self.assertIn("pass_Dirac_number_normalization_gate", payload["next_required"])
        self.assertIn("feed_result_to_Dirac_thermal_occupation_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
