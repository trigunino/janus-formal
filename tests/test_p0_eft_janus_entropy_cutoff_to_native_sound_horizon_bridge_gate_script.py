import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    entropy_cutoff_to_native_sound_horizon_bridge_payload,
)


class JanusEntropyCutoffToNativeSoundHorizonBridgeGateTests(unittest.TestCase):
    def test_entropy_cutoff_supplies_lower_bound(self):
        payload = entropy_cutoff_to_native_sound_horizon_bridge_payload()
        self.assertAlmostEqual(payload["entropy_cutoff"]["a_min"], 1.0 / 1001.0)
        self.assertTrue(payload["entropy_cutoff"]["pre_drag_reach"])
        self.assertTrue(payload["sound_horizon_contract_updated"]["zero_lower_limit_divergence_avoided"])

    def test_bao_is_still_not_executable(self):
        payload = entropy_cutoff_to_native_sound_horizon_bridge_payload()
        remaining = payload["remaining_inputs_after_cutoff"]
        self.assertFalse(remaining["derive_drag_epoch_a_d"])
        self.assertFalse(remaining["derive_H_J_of_a"])
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
