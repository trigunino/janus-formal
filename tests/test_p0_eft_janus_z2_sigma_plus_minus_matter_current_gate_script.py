import unittest

from scripts.build_p0_eft_janus_z2_sigma_plus_minus_matter_current_gate import build_payload


class P0EFTJanusZ2SigmaPlusMinusMatterCurrentGateTests(unittest.TestCase):
    def test_plus_minus_current_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["plus_minus_matter_current_ledger_declared"])
        self.assertTrue(payload["declared"]["plus_minus_Dirac_matter_action_gate_declared"])
        self.assertTrue(payload["declared"]["projected_Dirac_matter_current_gate_declared"])
        self.assertTrue(payload["declared"]["Dirac_current_formula_imported"])
        self.assertTrue(payload["declared"]["plus_current_declared"])
        self.assertTrue(payload["declared"]["minus_current_declared"])

    def test_currents_wait_for_active_matter_actions(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_matter_action_ready"])
        self.assertFalse(payload["closure"]["minus_matter_action_ready"])
        self.assertFalse(payload["closure"]["plus_minus_matter_currents_ready"])
        self.assertFalse(payload["plus_minus_matter_current_ready"])
        self.assertIn("pass_plus_minus_Dirac_matter_action_gate", payload["next_required"])
        self.assertIn("pass_projected_Dirac_matter_current_gate", payload["next_required"])
        self.assertIn("derive_J_plus_and_J_minus_from_Noether_variation", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
