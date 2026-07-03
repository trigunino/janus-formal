import unittest

from scripts.build_p0_eft_janus_rp4_pin_sign_audit_gate import build_payload


class P0EFTJanusRP4PinSignAuditGateTests(unittest.TestCase):
    def test_rp4_pin_sign_computed_but_sigma_aps_lift_blocks_closure(self):
        payload = build_payload()

        self.assertTrue(payload["global_base_is_rp4"])
        self.assertTrue(payload["rp2_boy_shadow_not_used_as_global_pin_proof"])
        self.assertTrue(payload["pin_sign_computed_for_rp4"])
        self.assertTrue(payload["rp4_base_pin_plus_exists"])
        self.assertFalse(payload["rp4_base_pin_minus_exists"])
        self.assertFalse(payload["sigma_aps_boundary_pin_lift_closed"])
        self.assertFalse(payload["pin_minus_lift_allowed"])
        self.assertFalse(payload["aps_pin_closure_allowed"])


if __name__ == "__main__":
    unittest.main()
