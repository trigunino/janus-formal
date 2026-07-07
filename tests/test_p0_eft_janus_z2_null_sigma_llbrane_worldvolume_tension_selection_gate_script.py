import unittest

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_worldvolume_tension_selection_gate import (
    build_payload,
)


class NullSigmaLLBraneWorldvolumeTensionSelectionGateTests(unittest.TestCase):
    def test_worldvolume_eom_does_not_select_chi_magnitude(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["worldvolume_selection_ready"])
        self.assertTrue(payload["closure"]["a0_consistency_fixed"])
        self.assertTrue(payload["closure"]["einstein_matching_relates_m_to_chi"])
        self.assertFalse(
            payload["closure"]["chi_magnitude_selected_by_local_worldvolume_eom"]
        )
        self.assertIn(
            "derive_Janus_PT_boundary_state_condition_for_chi_LL",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
