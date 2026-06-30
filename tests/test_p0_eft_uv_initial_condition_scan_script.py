from __future__ import annotations

import unittest

from scripts.run_p0_eft_uv_initial_condition_scan import run_scan


class P0EFTUVInitialConditionScanTests(unittest.TestCase):
    def test_uv_scan_runs(self) -> None:
        payload = run_scan()

        self.assertEqual(payload["status"], "uv-initial-condition-scan-computed")
        self.assertIn("best", payload)
        self.assertGreater(len(payload["rows"]), 10)


if __name__ == "__main__":
    unittest.main()
