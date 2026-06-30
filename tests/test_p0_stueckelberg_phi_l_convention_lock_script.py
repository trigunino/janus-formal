from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_phi_l_convention_lock import build_payload


class P0PhiLConventionLockTests(unittest.TestCase):
    def test_convention_lock_keeps_prediction_blocked(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["conventions_locked_as_requirements"])
        self.assertTrue(decision["dust_branch_can_be_tested"])
        self.assertFalse(decision["dust_branch_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rules_forbid_map_and_volume_rustines(self) -> None:
        payload = build_payload()
        rules = " ".join(row["rule"] for row in payload["locked_conventions"])
        failures = " ".join(payload["failure_modes"])

        self.assertIn("same L", rules)
        self.assertIn("B rho", rules)
        self.assertIn("another map for Q_cross", failures)
        self.assertIn("double counting", failures)

    def test_projected_dust_identity_is_required(self) -> None:
        payload = build_payload()
        needed = " ".join(row["needed_for"] for row in payload["locked_conventions"])

        self.assertIn("rho h Cuu", needed)
        self.assertIn("mirror residuals", needed)


if __name__ == "__main__":
    unittest.main()
