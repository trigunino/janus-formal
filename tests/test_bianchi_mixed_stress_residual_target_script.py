from __future__ import annotations

import unittest

from scripts.build_bianchi_mixed_stress_residual_target import build_payload


class BianchiMixedStressResidualTargetTests(unittest.TestCase):
    def test_residual_target_is_not_physics_closure(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "derivation-target")
        self.assertFalse(payload["physics_closed"])
        self.assertIn("C^mu_{nu a}", payload["hard_missing_term"])

    def test_both_residuals_have_zero_closure_targets(self) -> None:
        payload = build_payload()
        residuals = {row["sector"]: row for row in payload["residuals"]}

        self.assertEqual(residuals["positive"]["closure"], "R_plus^mu = 0")
        self.assertEqual(residuals["negative"]["closure"], "R_minus^mu = 0")
        self.assertIn("B_plus", residuals["positive"]["residual"])
        self.assertIn("B_minus", residuals["negative"]["residual"])

    def test_qcross_cannot_bypass_both_residuals(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_uses"])
        optical = " ".join(payload["optical_slot"])

        self.assertIn("K_plus/K_minus", optical)
        self.assertIn("R_plus^mu=0", forbidden)
        self.assertIn("R_minus^mu=0", forbidden)
        self.assertIn("do not absorb Q_cross", forbidden)


if __name__ == "__main__":
    unittest.main()
