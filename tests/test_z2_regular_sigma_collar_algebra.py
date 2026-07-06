from __future__ import annotations

import unittest

from src.janus_lab.z2_regular_sigma_collar_algebra import regular_sigma_collar_algebra_payload


class Z2RegularSigmaCollarAlgebraTests(unittest.TestCase):
    def test_default_regular_collar_allows_hk_pipeline(self) -> None:
        payload = regular_sigma_collar_algebra_payload()

        self.assertTrue(payload["full_collar_block_non_degenerate"])
        self.assertTrue(payload["induced_h_ab_non_degenerate"])
        self.assertTrue(payload["regular_hK_pipeline_allowed"])

    def test_horizon_A0_zero_blocks_regular_hk_pipeline(self) -> None:
        payload = regular_sigma_collar_algebra_payload(A0=0.0, B0=2.0, C0=-1.0)

        self.assertTrue(payload["full_collar_block_non_degenerate"])
        self.assertFalse(payload["induced_h_ab_non_degenerate"])
        self.assertFalse(payload["regular_hK_pipeline_allowed"])


if __name__ == "__main__":
    unittest.main()
