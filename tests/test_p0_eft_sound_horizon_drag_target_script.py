from __future__ import annotations

import unittest

from scripts.build_p0_eft_sound_horizon_drag_target import build_payload


class P0EFTSoundHorizonDragTargetTests(unittest.TestCase):
    def test_sound_horizon_target_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "sound-horizon-drag-target-encoded")
        self.assertTrue(payload["passes_bao_shape_gate"])
        self.assertLess(payload["required_rd_ratio"], 1.0)
        self.assertGreater(payload["uniform_drag_epoch_hubble_boost"], 1.0)

    def test_target_is_not_claimed_as_derived(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["is_derived_geometry"])
        self.assertGreater(payload["required_fractional_E2_excess"], 0.0)
        self.assertIn("drag-epoch", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
