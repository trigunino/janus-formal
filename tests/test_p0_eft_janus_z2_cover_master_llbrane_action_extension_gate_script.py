import unittest

from scripts.build_p0_eft_janus_z2_cover_master_llbrane_action_extension_gate import (
    build_payload,
)


class Z2CoverMasterLLBraneActionExtensionGateTests(unittest.TestCase):
    def test_master_action_extension_does_not_select_chi_without_state(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["active_core"], "JanusZ2CoverMasterAction")
        self.assertTrue(payload["closure"]["single_master_action_retained"])
        self.assertTrue(payload["closure"]["LL_brane_worldvolume_added_on_Sigma"])
        self.assertFalse(
            payload["closure"]["chi_magnitude_selected_by_global_variation"]
        )
        self.assertFalse(
            payload["closure"]["chi_magnitude_selected_by_boundary_state"]
        )
        self.assertIn(
            "derive_boundary_state_or_quantization_condition_for_chi_LL",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
