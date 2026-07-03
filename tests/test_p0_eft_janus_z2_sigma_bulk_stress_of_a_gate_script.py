import unittest

from scripts.build_p0_eft_janus_z2_sigma_bulk_stress_of_a_gate import build_payload


class P0EFTJanusZ2SigmaBulkStressOfAGateTests(unittest.TestCase):
    def test_bulk_stress_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["bulk_stress_ledger_declared"])
        self.assertTrue(payload["declared"]["sector_density_pressure_gate_declared"])
        self.assertTrue(payload["declared"]["Holst_torsion_stress_gate_declared"])
        self.assertIn("perfect_fluid", payload["formula"])
        self.assertTrue(payload["declared"]["observational_fit_forbidden"])

    def test_bulk_stress_of_a_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_matter_density_pressure_of_a_ready"])
        self.assertFalse(payload["closure"]["torsion_stress_of_a_ready"])
        self.assertFalse(payload["bulk_stress_of_a_ready"])
        self.assertIn("pass_sector_density_pressure_of_a_gate", payload["next_required"])
        self.assertIn("pass_Holst_torsion_stress_of_a_gate", payload["next_required"])
        self.assertIn("assemble_T_plus_minus_munu_of_a", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
