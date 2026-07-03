import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_mass_temperature_law_of_a_gate import build_payload


class P0EFTJanusZ2SigmaDiracMassTemperatureLawOfAGateTests(unittest.TestCase):
    def test_mass_temperature_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_mass_temperature_ledger_declared"])
        self.assertTrue(payload["declared"]["momentum_redshift_law_imported"])
        self.assertTrue(payload["declared"]["massive_decoupled_Fermi_gas_guard_declared"])
        self.assertTrue(payload["declared"]["Dirac_regime_selection_gate_declared"])
        self.assertTrue(payload["declared"]["Dirac_decoupling_condition_gate_declared"])
        self.assertIn("distribution_energy", payload["formulas"])

    def test_mass_temperature_law_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["relativistic_or_massive_regime_derived"])
        self.assertFalse(payload["closure"]["decoupling_scale_derived"])
        self.assertFalse(payload["dirac_mass_temperature_law_of_a_ready"])
        self.assertIn("pass_Dirac_regime_selection_gate", payload["next_required"])
        self.assertIn("pass_Dirac_decoupling_condition_gate", payload["next_required"])
        self.assertIn("propagate_mass_temperature_law_to_fermion_distribution_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
