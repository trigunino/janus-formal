import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_alpha_res_z2_anti_invariance_obligation_gate import (
    build_payload,
)


class CountertermAlphaResZ2AntiInvarianceObligationGateTests(unittest.TestCase):
    def test_alpha_res_z2_anti_invariance_route_is_credible_but_blocked(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["route"], "Z2_odd_residual_projection")
        self.assertTrue(payload["declared"]["anti_invariance_obligation_declared"])
        self.assertTrue(payload["channel_tests"]["orientation_normal_channel"]["ready"])
        self.assertTrue(payload["channel_tests"]["holst_torsion_channel"]["ready"])
        self.assertTrue(payload["closure"]["alpha_res_components_available"])
        self.assertTrue(payload["closure"]["alpha_res_component_decomposition_available"])
        self.assertFalse(payload["closure"]["alpha_res_component_values_available"])
        self.assertTrue(payload["closure"]["all_components_declared"])
        self.assertTrue(payload["closure"]["paired_sheet_residual_support_proved"])
        self.assertTrue(payload["component_parity_tests"]["torsion_pullback_component"]["parity_proved"])
        self.assertTrue(payload["component_parity_tests"]["spinor_component"]["parity_proved"])
        self.assertTrue(payload["channel_tests"]["spinor_current_channel"]["ready"])
        self.assertFalse(payload["component_parity_tests"]["metric_tetrad_component"]["parity_proved"])
        self.assertFalse(payload["closure"]["all_emitted_components_odd"])
        self.assertFalse(payload["closure"]["alpha_res_Z2_anti_invariance_proved"])
        self.assertFalse(payload["closure"]["E_counterterm_zero_without_density"])
        self.assertEqual(payload["route_status"], "credible_but_blocked")
        self.assertEqual(payload["primary_blocker"], "componentwise_parity_proofs")
        self.assertNotIn("paired_sheet_residual_support", payload["blockers"])
        self.assertNotIn("prove_paired_sheet_residual_support_on_Sigma", payload["next_required"])
        self.assertIn("tau_Z2^* alpha_res", payload["formulae"]["target"])


if __name__ == "__main__":
    unittest.main()
