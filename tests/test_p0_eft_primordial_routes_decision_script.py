from __future__ import annotations

import unittest

from scripts.build_p0_eft_primordial_routes_decision import build_payload


class P0EFTPrimordialRoutesDecisionTests(unittest.TestCase):
    def test_visibility_improves_but_does_not_solve(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "primordial-routes-decision-recorded")
        self.assertTrue(payload["nonlocal_visibility_improves_total_chi2"])
        self.assertFalse(payload["nonlocal_visibility_fixes_lowE"])
        self.assertTrue(payload["highl_still_bad_after_visibility"])
        self.assertTrue(payload["tested_routes_excluded_as_sufficient"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
