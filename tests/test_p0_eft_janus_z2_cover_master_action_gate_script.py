import unittest

from scripts.derive_p0_eft_janus_z2_cover_master_action_gate import build_payload


class JanusZ2CoverMasterActionGateTests(unittest.TestCase):
    def test_declares_single_action_route_and_forbids_shortcuts(self):
        payload = build_payload()
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["active_core"], "JanusZ2CoverMasterAction")
        self.assertTrue(payload["master_action_contract_declared"])
        self.assertFalse(payload["master_action_derivation_complete"])
        self.assertTrue(payload["guardrails"]["one_action_not_two_independent_actions"])
        self.assertTrue(payload["guardrails"]["rho_eff_shortcut_forbidden"])
        self.assertTrue(payload["guardrails"]["thermodynamic_negative_density_forbidden"])
        self.assertFalse(payload["guardrails"]["z4_monodromy_assumed"])
        self.assertFalse(payload["guardrails"]["observational_fit_used"])
        self.assertIn("sigma_junction", payload["projection_targets"])


if __name__ == "__main__":
    unittest.main()
