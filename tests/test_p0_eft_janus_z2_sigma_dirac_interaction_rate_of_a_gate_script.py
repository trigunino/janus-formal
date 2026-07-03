import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_interaction_rate_of_a_gate import build_payload


class P0EFTJanusZ2SigmaDiracInteractionRateOfAGateTests(unittest.TestCase):
    def test_interaction_rate_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_interaction_rate_ledger_declared"])
        self.assertTrue(payload["declared"]["Gamma_equals_number_density_times_thermal_cross_section_imported"])
        self.assertTrue(payload["declared"]["thermal_cross_section_gate_declared"])
        self.assertIn("plus_rate", payload["formulas"])

    def test_interaction_rate_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_thermal_cross_section_of_a_ready"])
        self.assertFalse(payload["closure"]["projected_interaction_rate_of_a_ready"])
        self.assertFalse(payload["dirac_interaction_rate_of_a_ready"])
        self.assertIn("pass_Dirac_thermal_cross_section_of_a_gate", payload["next_required"])
        self.assertIn("feed_Gamma_plus_minus_to_Dirac_decoupling_condition_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
