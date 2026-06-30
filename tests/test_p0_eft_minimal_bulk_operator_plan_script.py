from __future__ import annotations

import unittest

from scripts.build_p0_eft_minimal_bulk_operator_plan import build_payload, render_markdown


class P0EFTMinimalBulkOperatorPlanTests(unittest.TestCase):
    def test_operator_plan_is_not_heat_kernel_result(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["minimal_operator_plan_written"])
        self.assertTrue(status["operator_chosen_for_first_test"])
        self.assertFalse(status["actual_heat_kernel_coefficients_computed"])
        self.assertFalse(status["prediction_ready"])

    def test_dirac_cartan_is_recommended_first_test(self) -> None:
        recommended = build_payload()["recommended_first_test"]

        self.assertEqual(recommended["operator"], "D_dirac_cartan")
        self.assertIn("spin connection and torsion", recommended["why"])

    def test_scalar_operator_not_enough(self) -> None:
        operators = {row["id"]: row for row in build_payload()["candidate_operators"]}

        self.assertFalse(operators["D_scalar"]["can_generate_double_dual"])
        self.assertEqual(operators["D_dirac_cartan"]["can_generate_double_dual"], "possible")

    def test_markdown_names_next_symbolic_step(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Dirac-Cartan", markdown)
        self.assertIn("a2/a4", markdown)


if __name__ == "__main__":
    unittest.main()
