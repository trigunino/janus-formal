from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_popt_acceptance_criteria import build_payload


class P0PoptAcceptanceCriteriaTests(unittest.TestCase):
    def test_criteria_defined_but_projector_not_constructed(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["acceptance_criteria_defined"])
        self.assertFalse(decision["popt_constructed"])
        self.assertFalse(payload["prediction_ready"])

    def test_criteria_require_same_transport_and_no_fit(self) -> None:
        payload = build_payload()
        criteria = " ".join(row["requirement"] for row in payload["criteria"])

        self.assertIn("same L", criteria)
        self.assertIn("same L and distribution", criteria)
        self.assertIn("no A_fit", criteria)

    def test_rejections_keep_qdet_out_of_lensing_strength(self) -> None:
        payload = build_payload()
        rejected = " ".join(payload["rejected"])

        self.assertIn("Q_det", rejected)
        self.assertIn("observed lensing", rejected)


if __name__ == "__main__":
    unittest.main()
