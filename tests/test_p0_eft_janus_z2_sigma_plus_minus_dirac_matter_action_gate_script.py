import unittest

from scripts.build_p0_eft_janus_z2_sigma_plus_minus_dirac_matter_action_gate import build_payload


class P0EFTJanusZ2SigmaPlusMinusDiracMatterActionGateTests(unittest.TestCase):
    def test_dirac_matter_action_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["plus_minus_dirac_matter_action_ledger_declared"])
        self.assertTrue(payload["declared"]["curved_Dirac_action_bibliography_checked"])
        self.assertTrue(payload["declared"]["Holst_fermion_bibliography_checked"])
        self.assertTrue(payload["declared"]["spinor_bundle_projection_gate_declared"])
        self.assertTrue(payload["declared"]["plus_Dirac_action_declared"])
        self.assertTrue(payload["declared"]["minus_Dirac_action_declared"])

    def test_actions_wait_for_pullback_and_spinor_data(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["coframe_connection_pullback_ready"])
        self.assertFalse(payload["closure"]["plus_spinor_data_ready"])
        self.assertFalse(payload["closure"]["plus_minus_matter_actions_ready"])
        self.assertFalse(payload["plus_minus_dirac_matter_action_ready"])
        self.assertIn("pass_coframe_connection_pullback_gate", payload["next_required"])
        self.assertIn("pass_spinor_bundle_projection_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
