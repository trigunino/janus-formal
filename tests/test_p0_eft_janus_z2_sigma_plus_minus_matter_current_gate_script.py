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

    def test_currents_follow_from_active_matter_actions(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["plus_matter_action_ready"])
        self.assertTrue(payload["closure"]["minus_matter_action_ready"])
        self.assertTrue(payload["closure"]["plus_minus_matter_currents_ready"])
        self.assertTrue(payload["plus_minus_matter_current_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertIn("keep_normal_flux_and_density_laws_separate_from_Noether_current", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
