import unittest

from scripts.build_p0_eft_janus_z2_sigma_spin_current_of_a_gate import build_payload


class P0EFTJanusZ2SigmaSpinCurrentOfAGateTests(unittest.TestCase):
    def test_spin_current_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["spin_current_ledger_declared"])
        self.assertTrue(payload["declared"]["Dirac_axial_current_relation_declared"])
        self.assertTrue(payload["declared"]["fermion_distribution_of_a_gate_declared"])
        self.assertTrue(payload["declared"]["observational_fit_forbidden"])
        self.assertIn("canonical_spin_tensor", payload["formulas"])

    def test_spin_current_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["fermion_distribution_of_a_ready"])
        self.assertFalse(payload["closure"]["projected_spin_current_of_a_ready"])
        self.assertFalse(payload["spin_current_of_a_ready"])
        self.assertIn("pass_fermion_distribution_of_a_gate", payload["next_required"])
        self.assertIn("propagate_spin_current_to_torsion_field_solution_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
