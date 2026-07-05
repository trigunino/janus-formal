import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_regime_selection_gate import build_payload


class P0EFTJanusZ2SigmaDiracRegimeSelectionGateTests(unittest.TestCase):
    def test_regime_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_regime_ledger_declared"])
        self.assertTrue(payload["declared"]["mass_over_decoupling_temperature_criterion_declared"])
        self.assertTrue(payload["declared"]["Dirac_decoupling_condition_gate_declared"])
        self.assertIn("semi_relativistic", payload["criteria"])

    def test_regime_selection_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_m_over_Tdec_derived"])
        self.assertFalse(payload["closure"]["projected_regime_selected"])
        self.assertFalse(payload["dirac_regime_selection_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "mass_temperature_ratio_from_active_distribution")
        self.assertIn("pass_Dirac_decoupling_condition_gate", payload["next_required"])
        self.assertIn("propagate_regime_to_mass_temperature_law_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
