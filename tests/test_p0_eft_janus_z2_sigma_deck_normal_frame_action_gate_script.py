import unittest

from scripts.derive_p0_eft_janus_z2_sigma_deck_normal_frame_action_gate import build_payload


class JanusZ2SigmaDeckNormalFrameActionGateTest(unittest.TestCase):
    def test_deck_reverses_normal_but_does_not_fix_radius(self):
        payload = build_payload()
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["deck_action"]["normal_line_deck_matrix"], [[-1.0]])
        self.assertTrue(payload["derived_now"]["deck_frame_map_lambda_ready"])
        self.assertFalse(payload["derived_now"]["collar_connection_omega_perp_ready"])
        self.assertFalse(payload["derived_now"]["R_Sigma_over_ell_collar_fixed"])


if __name__ == "__main__":
    unittest.main()
