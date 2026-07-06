import unittest

from scripts.derive_p0_eft_janus_z2_sigma_homothetic_collar_no_radius_selection import (
    build_payload,
)


class JanusZ2SigmaHomotheticCollarNoRadiusSelectionScriptTest(unittest.TestCase):
    def test_homothetic_class_does_not_select_radius(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["extension_allowed"])
        self.assertFalse(payload["radius_selection_ready"])
        self.assertFalse(payload["R_Sigma_solution_certificate_ready"])
        for status in payload["case_status"].values():
            self.assertTrue(status["F_reg_lambda_independent"])
            self.assertFalse(status["radius_selection_possible"])


if __name__ == "__main__":
    unittest.main()
