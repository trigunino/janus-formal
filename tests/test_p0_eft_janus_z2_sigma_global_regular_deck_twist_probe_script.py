import unittest

from scripts.derive_p0_eft_janus_z2_sigma_global_regular_deck_twist_probe import (
    build_payload,
)


class JanusZ2SigmaGlobalRegularDeckTwistProbeScriptTest(unittest.TestCase):
    def test_deck_twist_defect_is_not_radius_selecting(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["extension_allowed"])
        self.assertEqual(payload["regularity_roots"], [])
        self.assertFalse(payload["R_Sigma_over_ell_collar_selected"])
        self.assertFalse(payload["radius_selection_ready"])
        self.assertTrue(all(value > 0.0 for value in payload["F_reg"]))
        self.assertEqual(len(set(payload["F_reg"])), 1)


if __name__ == "__main__":
    unittest.main()
