import unittest

from scripts.build_p0_eft_janus_z2_sigma_projective_gluing_normal_orientation_sign_gate import build_payload


class P0EFTJanusZ2SigmaProjectiveGluingNormalOrientationSignGateTests(unittest.TestCase):
    def test_projective_gluing_orientation_sign_is_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["projective_gluing_normal_orientation_sign_ledger_declared"])
        self.assertTrue(payload["closure"]["z2_normal_orientation_sign_fixed"])
        self.assertTrue(payload["projective_gluing_normal_orientation_sign_ready"])

    def test_orientation_sign_is_not_fitted(self):
        payload = build_payload()

        self.assertEqual(payload["formulae"]["orientation_coefficient"], "epsilon_Z2 = -1")
        self.assertIn("manual Sigma orientation sign", payload["forbidden"])
        self.assertIn("observationally fitted orientation sign", payload["forbidden"])


if __name__ == "__main__":
    unittest.main()
