from __future__ import annotations

import unittest

from scripts.build_p0_eft_desi_dr2_bao_gate import build_payload


class P0EFTDESIDR2BAOGateTests(unittest.TestCase):
    def test_desi_bao_data_and_covariance_load(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "desi-dr2-bao-loaded-holst-distance-map-open")
        self.assertGreater(payload["data_points"], 0)
        self.assertTrue(payload["covariance_is_symmetric"])
        self.assertTrue(payload["covariance_is_positive_definite"])

    def test_lcdm_control_is_finite_and_holst_is_blocked(self) -> None:
        payload = build_payload()

        self.assertGreater(payload["best_lcdm_control"]["chi2"], 0.0)
        self.assertTrue(payload["holst_bao_shape_diagnostic_scored"])
        self.assertGreater(payload["holst_bao_shape_diagnostic"]["chi2"], 0.0)
        self.assertIn("holst_bao_shape_diagnostic_passes", payload)
        self.assertFalse(payload["holst_growth_branch_bao_scored"])
        self.assertTrue(payload["janus_holst_late_distance_map_ready"])
        self.assertFalse(payload["janus_holst_distance_ruler_map_ready"])
        self.assertIn("D_M", payload["holst_bao_blocker"])


if __name__ == "__main__":
    unittest.main()
