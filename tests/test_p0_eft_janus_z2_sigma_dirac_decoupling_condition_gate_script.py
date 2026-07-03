import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_decoupling_condition_gate import build_payload


class P0EFTJanusZ2SigmaDiracDecouplingConditionGateTests(unittest.TestCase):
    def test_decoupling_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_decoupling_ledger_declared"])
        self.assertTrue(payload["declared"]["Gamma_equals_H_criterion_imported"])
        self.assertTrue(payload["declared"]["interaction_rate_gate_declared"])
        self.assertTrue(payload["declared"]["numerical_background_closure_gate_declared"])
        self.assertIn("plus_decoupling", payload["formulas"])

    def test_decoupling_condition_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_interaction_rate_of_a_ready"])
        self.assertFalse(payload["closure"]["H_Z2Sigma_of_a_ready"])
        self.assertFalse(payload["dirac_decoupling_condition_ready"])
        self.assertIn("pass_Dirac_interaction_rate_of_a_gate", payload["next_required"])
        self.assertIn("pass_Z2Sigma_numerical_background_closure_gate", payload["next_required"])
        self.assertIn("derive_active_H_Z2Sigma_of_a", payload["next_required"])
        self.assertIn("propagate_decoupling_scales_to_regime_and_temperature_gates", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
