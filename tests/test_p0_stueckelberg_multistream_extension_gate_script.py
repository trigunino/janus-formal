from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_multistream_extension_gate import build_payload


class P0MultistreamExtensionGateTests(unittest.TestCase):
    def test_post_caustic_not_closed_but_pre_caustic_allowed(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertFalse(decision["post_caustic_closure_available"])
        self.assertTrue(decision["pre_caustic_diagnostic_allowed"])
        self.assertTrue(decision["sheet_sum_is_next_nonfit_extension"])
        self.assertFalse(payload["prediction_ready"])

    def test_smooth_caustic_fit_is_forbidden(self) -> None:
        payload = build_payload()
        smooth = [row for row in payload["options"] if row["name"] == "smooth_caustic_fit"][0]

        self.assertFalse(smooth["admissible"])
        self.assertIn("forbidden fit", smooth["prediction_scope"])

    def test_sheet_sum_keeps_no_independent_normalization(self) -> None:
        payload = build_payload()
        requirements = " ".join(payload["required_for_sheet_sum"])

        self.assertIn("no independent", requirements)
        self.assertIn("Q_cross", requirements)
        self.assertIn("mirror inverse", requirements)


if __name__ == "__main__":
    unittest.main()
