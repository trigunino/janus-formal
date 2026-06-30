from __future__ import annotations

import unittest

from scripts.build_p0_pure_gauge_pde_consistency_check import build_payload


class P0PureGaugePdeConsistencyCheckTests(unittest.TestCase):
    def test_check_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["check_written"])
        self.assertTrue(payload["lorentz_admissible_conditionally"])
        self.assertFalse(payload["zero_divergence_automatic"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_required_equalities_include_both_sectors_and_qcross(self) -> None:
        text = " ".join(build_payload()["required_equalities"])

        self.assertIn("D_plus_nu(B_plus L_-+ T_minus", text)
        self.assertIn("D_minus_nu(B_minus L_+- T_plus", text)
        self.assertIn("Q_cross", text)
        self.assertIn("Lorentz projection", text)

    def test_pass_fail_says_pde_not_automatic(self) -> None:
        rows = {row["check"]: row for row in build_payload()["pass_fail"]}

        self.assertIn("by construction", rows["Lorentz admissibility"]["status"])
        self.assertIn("not automatic", rows["zero-divergence PDE"]["status"])
        self.assertFalse(any(row["closes_physics"] for row in rows.values()))


if __name__ == "__main__":
    unittest.main()
