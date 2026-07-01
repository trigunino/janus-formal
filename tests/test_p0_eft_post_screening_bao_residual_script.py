from __future__ import annotations

import unittest

from scripts.build_p0_eft_post_screening_bao_residual import run_scan


class P0EFTPostScreeningBAOResidualTests(unittest.TestCase):
    def test_post_screening_scan_runs(self) -> None:
        payload = run_scan()

        self.assertEqual(payload["status"], "post-screening-bao-residual-scan-computed")
        self.assertEqual(payload["xi_bg"], 0.0)
        self.assertEqual(payload["xi_growth"], 1.0)
        self.assertGreater(len(payload["rows"]), 1)

    def test_best_reports_matter_and_ruler(self) -> None:
        best = run_scan()["best"]

        self.assertIn("Omega_m_bg", best)
        self.assertIn("ruler_scale_fit", best)
        self.assertGreater(best["ruler_scale_fit"], 0.0)


if __name__ == "__main__":
    unittest.main()
