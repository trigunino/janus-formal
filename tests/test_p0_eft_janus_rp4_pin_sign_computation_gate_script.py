import unittest

from scripts.build_p0_eft_janus_rp4_pin_sign_computation_gate import build_payload


class P0EFTJanusRP4PinSignComputationGateTests(unittest.TestCase):
    def test_rp4_base_pin_sign_is_computed_but_sigma_aps_remains_open(self):
        payload = build_payload()

        self.assertEqual(payload["global_base"], "RP4")
        self.assertTrue(payload["w1_nonzero"])
        self.assertTrue(payload["w2_zero"])
        self.assertTrue(payload["w1_squared_nonzero"])
        self.assertTrue(payload["rp4_base_pin_plus_exists"])
        self.assertFalse(payload["rp4_base_pin_minus_exists"])
        self.assertTrue(payload["rp4_base_pin_sign_computed"])
        self.assertFalse(payload["sigma_aps_boundary_pin_lift_closed"])
        self.assertFalse(payload["aps_pin_closure_allowed"])


if __name__ == "__main__":
    unittest.main()
