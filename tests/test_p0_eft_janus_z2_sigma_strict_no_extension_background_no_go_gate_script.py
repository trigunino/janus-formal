import unittest

from scripts.build_p0_eft_janus_z2_sigma_strict_no_extension_background_no_go_gate import (
    build_payload,
)


class StrictNoExtensionBackgroundNoGoGateTests(unittest.TestCase):
    def test_strict_no_extension_closed_background_is_no_go(self):
        payload = build_payload()
        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["rho_eff_zero_on_grid"])
        self.assertTrue(payload["closed_positive_curvature_term_negative"])
        self.assertTrue(payload["E2_negative_on_grid"])
        self.assertTrue(payload["strict_no_extension_background_no_go"])
        self.assertFalse(payload["full_no_fit_cosmology_ready"])


if __name__ == "__main__":
    unittest.main()
