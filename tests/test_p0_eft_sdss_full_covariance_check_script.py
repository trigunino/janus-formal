from __future__ import annotations

import unittest

from scripts.build_p0_eft_sdss_full_covariance_check import build_payload


class P0EFTSDSSFullCovarianceCheckTests(unittest.TestCase):
    def test_full_covariance_check_scores_holst_branch(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "sdss-full-covariance-computed")
        self.assertEqual(payload["data_points"], 5)
        self.assertGreater(payload["chi2_unit_amplitude_full_covariance"], 0.0)
        self.assertGreater(payload["chi2_best_amplitude_full_covariance"], 0.0)

    def test_branch_is_geometric_lock_candidate(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["branch"]["eta_holst"], -2.0)
        self.assertEqual(payload["branch"]["z_sigma"], 0.5)


if __name__ == "__main__":
    unittest.main()
