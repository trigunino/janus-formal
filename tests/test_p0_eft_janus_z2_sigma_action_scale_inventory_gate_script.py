import unittest

from scripts.build_p0_eft_janus_z2_sigma_action_scale_inventory_gate import (
    build_payload,
)


class ActionScaleInventoryGateTests(unittest.TestCase):
    def test_active_action_inventory_has_no_length_selecting_term(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["any_action_scale_available"])
        self.assertFalse(payload["absolute_RSigma_from_action_ready"])
        self.assertTrue(payload["routes"]["einstein_hilbert_gravity_G"]["available"])
        self.assertFalse(
            payload["routes"]["einstein_hilbert_gravity_G"]["fixes_length_by_itself"]
        )
        self.assertFalse(
            payload["routes"]["cosmological_constant_or_potential"]["available"]
        )
        self.assertTrue(payload["routes"]["schwarzschild_PT_bridge_Rs"]["available"])
        self.assertFalse(
            payload["routes"]["schwarzschild_PT_bridge_Rs"]["fixes_length_by_itself"]
        )


if __name__ == "__main__":
    unittest.main()
