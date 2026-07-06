import unittest

from scripts.build_p0_eft_janus_z2_sigma_lapse_time_gauge_route_decision_gate import (
    build_payload,
)


class LapseTimeGaugeRouteDecisionGateTests(unittest.TestCase):
    def test_flrw_lapse_does_not_fix_dimensional_h0(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["restricted_FLRW_proper_time_lapse_ready"])
        self.assertFalse(payload["general_perturbed_lapse_slice_fixed"])
        self.assertTrue(payload["can_fix_branch_lapse_for_FLRW_background"])
        self.assertFalse(payload["can_fix_dimensional_H0"])
        self.assertIn("on-shell Hamiltonian", payload["why_H0_still_blocked"])
        self.assertIn("do_not_turn_FLRW_N_equals_1_into_numeric_H0", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
