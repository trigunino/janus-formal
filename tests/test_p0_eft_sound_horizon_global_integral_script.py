from __future__ import annotations

import unittest

from scripts.build_p0_eft_sound_horizon_global_integral import build_payload


class P0EFTSoundHorizonGlobalIntegralTests(unittest.TestCase):
    def test_global_sound_horizon_integral_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "sound-horizon-global-integral-computed")
        self.assertLess(payload["rd_ratio_janus_over_ref"], 1.0)
        self.assertGreater(payload["neff_janus"], payload["neff_ref"])

    def test_delta_neff_shortfall_is_explicit(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["matches_bao_required_shrink"])
        self.assertGreater(payload["delta_neff_shortfall"], 0.0)
        self.assertGreater(payload["required_delta_neff_for_bao_ratio"], payload["delta_neff_janus_holst"])
        self.assertFalse(payload["is_derived_geometry"])


if __name__ == "__main__":
    unittest.main()
