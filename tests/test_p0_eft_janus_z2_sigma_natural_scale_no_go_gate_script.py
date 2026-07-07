import unittest

from scripts.build_p0_eft_janus_z2_sigma_natural_scale_no_go_gate import (
    build_payload,
)


class NaturalScaleNoGoGateTests(unittest.TestCase):
    def test_planck_length_is_constructible_but_not_accepted_as_throat_scale(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["natural_scale_constructible"])
        self.assertFalse(payload["natural_scale_accepted_as_RSigma"])
        self.assertFalse(payload["action_scale_inventory"]["any_action_scale_available"])
        self.assertGreater(payload["candidate_natural_scale"]["value_m"], 0.0)
        self.assertIn(
            "janus_action_identifies_RSigma_with_planck_length",
            payload["blocked_by"],
        )


if __name__ == "__main__":
    unittest.main()
