from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_zero_param_progression import build_payload, render_markdown


class P0StueckelbergZeroParamProgressionTests(unittest.TestCase):
    def test_progression_records_partial_progress_not_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "progression-partial")
        self.assertEqual(payload["zero_parameter_branch"], "available")
        self.assertEqual(payload["structural_action_test"], "passed")
        self.assertFalse(payload["compatibility_closed"])
        self.assertFalse(payload["residuals_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_steps_include_closed_and_open_work(self) -> None:
        steps = {row["step"]: row for row in build_payload()["steps"]}

        self.assertTrue(steps["fix_phi_family"]["closed"])
        self.assertTrue(steps["write_explicit_action"]["closed"])
        self.assertFalse(steps["test_e_phi_e_l_compatibility"]["closed"])
        self.assertFalse(steps["substitute_residuals"]["closed"])

    def test_non_fit_constraints_are_explicit(self) -> None:
        constraints = " ".join(build_payload()["non_fit_constraints"])

        self.assertIn("no observational amplitude", constraints)
        self.assertIn("same phi/L", constraints)
        self.assertIn("M15/M30 sign recovery", constraints)

    def test_markdown_names_specific_blockers(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("E_phi/E_L compatibility", markdown)
        self.assertIn("residual substitution", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
