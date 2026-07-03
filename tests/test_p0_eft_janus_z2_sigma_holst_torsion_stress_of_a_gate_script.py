import unittest

from scripts.build_p0_eft_janus_z2_sigma_holst_torsion_stress_of_a_gate import build_payload


class P0EFTJanusZ2SigmaHolstTorsionStressOfAGateTests(unittest.TestCase):
    def test_holst_torsion_stress_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["holst_torsion_stress_ledger_declared"])
        self.assertTrue(payload["declared"]["torsion_field_solution_gate_declared"])
        self.assertTrue(payload["declared"]["Immirzi_profile_gate_declared"])
        self.assertTrue(payload["declared"]["stress_variation_formula_declared"])
        self.assertTrue(payload["declared"]["observational_fit_forbidden"])
        self.assertIn("stress_variation", payload["formulas"])

    def test_holst_torsion_stress_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["torsion_field_solution_of_a_ready"])
        self.assertFalse(payload["closure"]["Immirzi_profile_of_a_ready"])
        self.assertFalse(payload["holst_torsion_stress_of_a_ready"])
        self.assertIn("pass_Z2Sigma_torsion_field_solution_of_a_gate", payload["next_required"])
        self.assertIn("pass_Immirzi_profile_of_a_gate", payload["next_required"])
        self.assertIn("propagate_Holst_torsion_stress_to_bulk_stress_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
