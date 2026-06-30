from __future__ import annotations

import unittest

from scripts.build_p0_source_measure_selection_rules import build_payload


class P0SourceMeasureSelectionRulesTests(unittest.TestCase):
    def test_rules_exist_but_do_not_accept_prediction(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["selection_rules_written"])
        self.assertTrue(payload["single_convention_required"])
        self.assertIsNone(payload["accepted_rule"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rules_cover_4volume_3volume_and_effective_density(self) -> None:
        rules = {row["rule"] for row in build_payload()["selection_rules"]}

        self.assertIn("field-equation measure", rules)
        self.assertIn("dust slice measure", rules)
        self.assertIn("effective density measure", rules)

    def test_residual_tests_require_both_sectors_and_tensor_matter(self) -> None:
        tests = " ".join(build_payload()["residual_tests"])

        self.assertIn("R_plus", tests)
        self.assertIn("R_minus", tests)
        self.assertIn("pressure and Pi", tests)
        self.assertIn("Q_cross", tests)

    def test_forbidden_prevents_measure_mixing_and_double_counting(self) -> None:
        forbidden = " ".join(build_payload()["forbidden"])

        self.assertIn("mix B_4vol and V3_dust", forbidden)
        self.assertIn("rho_eff by Q_det", forbidden)
        self.assertIn("Q_cross as a source-density", forbidden)
        self.assertIn("drop lapse terms", forbidden)


if __name__ == "__main__":
    unittest.main()
