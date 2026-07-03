import unittest

from scripts.build_p0_eft_janus_z2_sigma_torsion_field_solution_of_a_gate import build_payload


class P0EFTJanusZ2SigmaTorsionFieldSolutionOfAGateTests(unittest.TestCase):
    def test_torsion_field_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["torsion_field_ledger_declared"])
        self.assertTrue(payload["declared"]["Sciama_Kibble_Cartan_equation_imported"])
        self.assertTrue(payload["declared"]["spin_current_of_a_gate_declared"])
        self.assertTrue(payload["declared"]["Immirzi_profile_gate_declared"])
        self.assertTrue(payload["declared"]["observational_fit_forbidden"])
        self.assertIn("cartan_constraint", payload["formulas"])

    def test_torsion_field_solution_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["spin_current_of_a_ready"])
        self.assertFalse(payload["closure"]["boundary_torsion_source_of_a_ready"])
        self.assertFalse(payload["torsion_field_solution_of_a_ready"])
        self.assertIn("pass_spin_current_of_a_gate", payload["next_required"])
        self.assertIn("pass_Immirzi_profile_of_a_gate", payload["next_required"])
        self.assertIn("propagate_torsion_solution_to_Holst_torsion_stress_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
