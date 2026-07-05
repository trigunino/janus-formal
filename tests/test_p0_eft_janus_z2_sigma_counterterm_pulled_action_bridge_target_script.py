import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_pulled_action_bridge_target import (
    build_payload,
)


class CountertermPulledActionBridgeTargetTests(unittest.TestCase):
    def test_pulled_sigma_counterterm_bridge_closes_action_but_not_inputs(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["pulled_dust_action_available"])
        self.assertTrue(payload["pulled_sigma_counterterm_action_bridge_closed"])
        self.assertFalse(payload["counterterm_local_density_action_inputs_allowed"])
        self.assertEqual(payload["primary_blocker"], "explicit_L_ct_coefficient_expansion")
        self.assertIn("compute_R_h_ab_R_K_ab_R_chi_from_S_ct_variation", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
