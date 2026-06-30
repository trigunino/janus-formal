from __future__ import annotations

import unittest

from scripts.run_p0_eft_anisotropic_pi_scan import run_scan


class P0EFTAnisotropicPiScanTests(unittest.TestCase):
    def test_anisotropic_scan_runs(self) -> None:
        payload = run_scan()

        self.assertEqual(payload["status"], "anisotropic-pi-scan-computed")
        self.assertIn("physical_count", payload)
        self.assertIn("best_unit_amplitude", payload)

    def test_pass_unit_count_is_reported(self) -> None:
        payload = run_scan()

        self.assertIn("pass_unit_count", payload)


if __name__ == "__main__":
    unittest.main()
