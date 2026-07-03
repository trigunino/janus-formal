import unittest

from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_action_reduction_gate import build_payload


class P0EFTJanusZ2SigmaProjectedDiracActionReductionGateTests(unittest.TestCase):
    def test_projected_dirac_action_reduction_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["projected_dirac_action_reduction_ledger_declared"])
        self.assertTrue(payload["declared"]["coframe_connection_pullback_gate_declared"])
        self.assertTrue(payload["declared"]["spinor_bundle_projection_gate_declared"])
        self.assertTrue(payload["declared"]["no_effective_fitted_mass_or_phase"])

    def test_reduction_waits_for_pullback_and_projection(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["coframe_connection_pullback_ready"])
        self.assertFalse(payload["closure"]["plus_minus_spinor_projection_ready"])
        self.assertFalse(payload["closure"]["Z2_projected_Dirac_action_ready"])
        self.assertFalse(payload["projected_dirac_action_reduction_ready"])
        self.assertIn("pass_spinor_bundle_projection_gate", payload["next_required"])
        self.assertIn("feed_projected_action_to_mass_term_from_action_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
