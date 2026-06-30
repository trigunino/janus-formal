from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_shear_distance_gauge_closure_gate import build_payload


class P0ShearDistanceGaugeClosureGateTests(unittest.TestCase):
    def test_distance_and_reduced_sign_closed_only_for_diagnostic(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["background_distance_closed_for_diagnostic"])
        self.assertTrue(decision["reduced_ricci_sign_closed_for_diagnostic"])
        self.assertFalse(decision["weyl_shear_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_branches_include_distance_shear_and_gauge(self) -> None:
        payload = build_payload()
        names = {row["name"] for row in payload["branches"]}

        self.assertIn("flrw_background_distance", names)
        self.assertIn("weyl_shear", names)
        self.assertIn("observer_source_gauge", names)

    def test_policy_forbids_standard_shear_import_and_gauge_fit(self) -> None:
        payload = build_payload()
        policy = " ".join(payload["output_policy"])

        self.assertIn("separate columns", policy)
        self.assertIn("standard GR", policy)
        self.assertIn("do not fit", policy)


if __name__ == "__main__":
    unittest.main()
