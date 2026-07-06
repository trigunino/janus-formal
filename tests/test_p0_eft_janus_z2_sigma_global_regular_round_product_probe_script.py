import unittest

from scripts.derive_p0_eft_janus_z2_sigma_global_regular_round_product_probe import (
    build_payload,
)


class JanusZ2SigmaGlobalRegularRoundProductProbeScriptTest(unittest.TestCase):
    def test_round_product_collar_regular_but_does_not_select_radius(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["extension_allowed"])
        self.assertEqual(payload["F_reg"], [0.0, 0.0, 0.0])
        self.assertEqual(payload["regularity_roots"], [0.5, 1.0, 2.0])
        self.assertFalse(payload["R_Sigma_over_ell_collar_selected"])
        self.assertFalse(payload["radius_selection_ready"])


if __name__ == "__main__":
    unittest.main()
