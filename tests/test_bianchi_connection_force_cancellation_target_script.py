from __future__ import annotations

import unittest

from scripts.build_bianchi_connection_force_cancellation_target import build_payload


class BianchiConnectionForceCancellationTargetTests(unittest.TestCase):
    def test_sufficient_conditions_are_written_but_not_closed(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["sufficient_conditions_written"])
        self.assertFalse(payload["conditions_source_derived"])
        self.assertFalse(payload["residuals_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_continuity_and_force_targets_cover_both_sectors(self) -> None:
        payload = build_payload()
        continuity = " ".join(payload["continuity_targets"])
        force = " ".join(payload["force_targets"])

        self.assertIn("D_minus_nu(rho_minus u_{-to+}^nu)=0", continuity)
        self.assertIn("D_plus_nu(rho_plus u_{+to-}^nu)=0", continuity)
        self.assertIn("+ C^mu_{nu a}", force)
        self.assertIn("- C^mu_{nu a}", force)

    def test_each_residual_has_sufficient_closure_row(self) -> None:
        rows = {row["sector"]: row for row in build_payload()["sufficient_closure"]}

        self.assertIn("R_plus^mu=0", rows["positive"]["then"])
        self.assertIn("R_minus^mu=0", rows["negative"]["then"])
        self.assertTrue(any("D_plus_nu T_plus" in item for item in rows["positive"]["if"]))
        self.assertTrue(any("D_minus_nu T_minus" in item for item in rows["negative"]["if"]))

    def test_shortcuts_remain_forbidden(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("do not assume D L=0 globally", forbidden)
        self.assertIn("do not drop connection-force", forbidden)
        self.assertIn("local Lorentz admissibility alone", forbidden)


if __name__ == "__main__":
    unittest.main()
