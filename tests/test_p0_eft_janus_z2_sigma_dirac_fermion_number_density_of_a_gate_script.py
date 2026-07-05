import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_fermion_number_density_of_a_gate import build_payload


class P0EFTJanusZ2SigmaDiracFermionNumberDensityOfAGateTests(unittest.TestCase):
    def test_dirac_number_density_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_number_density_ledger_declared"])
        self.assertTrue(payload["declared"]["FLRW_dilution_law_derived"])
        self.assertTrue(payload["declared"]["Dirac_number_normalization_gate_declared"])
        self.assertIn("flrw_dilution", payload["formulas"])

    def test_dirac_number_density_remains_open_on_normalizations(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_number_normalization_derived"])
        self.assertFalse(payload["closure"]["projected_number_density_ready"])
        self.assertFalse(payload["dirac_fermion_number_density_of_a_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertFalse(payload["upstream_frontiers"]["dirac_number_normalization"]["gate_passed"])
        self.assertIn("pass_Dirac_number_normalization_gate", payload["next_required"])
        self.assertIn("propagate_number_density_to_fermion_distribution_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
