import unittest

from scripts.build_p0_eft_janus_z2_sigma_fermion_distribution_of_a_gate import build_payload


class P0EFTJanusZ2SigmaFermionDistributionOfAGateTests(unittest.TestCase):
    def test_fermion_distribution_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["fermion_distribution_ledger_declared"])
        self.assertTrue(payload["declared"]["Dirac_gas_route_declared"])
        self.assertTrue(payload["declared"]["fermion_route_selection_gate_imported"])
        self.assertTrue(payload["declared"]["Dirac_number_density_gate_imported"])
        self.assertTrue(payload["declared"]["Dirac_mass_temperature_law_gate_imported"])
        self.assertTrue(payload["declared"]["Dirac_thermal_occupation_gate_imported"])
        self.assertTrue(payload["declared"]["Weyssenhoff_fluid_route_declared"])
        self.assertIn("number_conservation", payload["formulas"])

    def test_fermion_distribution_remains_open(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["route_selected_from_action_or_topology"])
        self.assertFalse(payload["closure"]["projected_fermion_distribution_of_a_ready"])
        self.assertFalse(payload["fermion_distribution_of_a_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertFalse(payload["upstream_frontiers"]["dirac_fermion_number_density_of_a"]["gate_passed"])
        self.assertIn("pass_Dirac_fermion_number_density_of_a_gate", payload["next_required"])
        self.assertIn("pass_Dirac_mass_temperature_law_of_a_gate", payload["next_required"])
        self.assertIn("pass_Dirac_thermal_occupation_of_a_gate", payload["next_required"])
        self.assertIn("propagate_fermion_distribution_to_spin_current_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
