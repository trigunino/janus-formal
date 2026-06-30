from __future__ import annotations

import unittest

from scripts.run_p0_eft_holst_immirzi_growth_solver import run_scan


class P0EFTHolstImmirziGrowthSolverTests(unittest.TestCase):
    def test_holst_scan_runs(self) -> None:
        payload = run_scan()

        self.assertEqual(payload["status"], "holst-immirzi-scan-computed")
        self.assertIn("best_unit_amplitude", payload)
        self.assertGreater(len(payload["rows"]), 10)


if __name__ == "__main__":
    unittest.main()
