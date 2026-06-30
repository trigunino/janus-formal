from __future__ import annotations

import unittest

from scripts.run_p0_eft_spinor_torsion_scan import run_scan, solve_omega_m0_with_spin


class P0EFTSpinorTorsionScanTests(unittest.TestCase):
    def test_spin_friedmann_solver_returns_positive_root_when_available(self) -> None:
        root = solve_omega_m0_with_spin(0.7, 0.25, -1.0)

        self.assertIsNotNone(root)
        self.assertGreater(root, 0)

    def test_spinor_scan_runs(self) -> None:
        payload = run_scan()

        self.assertEqual(payload["status"], "spinor-torsion-scan-computed")
        self.assertIn("physical_count", payload)
        self.assertIn("best_unit_amplitude", payload)


if __name__ == "__main__":
    unittest.main()
