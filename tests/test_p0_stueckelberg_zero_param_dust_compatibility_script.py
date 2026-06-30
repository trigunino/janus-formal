from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_zero_param_dust_compatibility import build_payload, render_markdown


class P0StueckelbergZeroParamDustCompatibilityTests(unittest.TestCase):
    def test_artifact_is_conditional_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "zero-param-dust-compatibility-conditional-open")
        self.assertFalse(payload["source_derived"])
        self.assertTrue(payload["new_axiom"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_zero_parameter_branch_has_no_fit_parameters(self) -> None:
        branch = build_payload()["branch"]

        self.assertEqual(branch["name"], "zero_parameter_normalized_copy")
        self.assertEqual(branch["free_parameters"], [])
        self.assertFalse(branch["fit_to_observations"])

    def test_conditions_include_dust_density_maps_and_map_equations(self) -> None:
        conditions = " ".join(
            row["name"] + " " + row["equation"] + " " + row["role"]
            for row in build_payload()["compatibility_conditions"]
        )

        self.assertIn("transported_plus_dust_continuity", conditions)
        self.assertIn("transported_minus_dust_continuity", conditions)
        self.assertIn("rho_minus_to_plus", conditions)
        self.assertIn("rho_plus_to_minus", conditions)
        self.assertIn("delta S / delta phi = 0", conditions)
        self.assertIn("delta S / delta L = 0", conditions)
        self.assertIn("same phi/L", conditions)

    def test_closure_decision_remains_false_but_conditional(self) -> None:
        decision = build_payload()["closure_decision"]

        self.assertFalse(decision["compatibility_closes"])
        self.assertTrue(decision["conditional_closure_possible"])
        self.assertIn("need not follow", decision["reason"])

    def test_markdown_reports_same_l_and_prediction_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("same_L_for_K_and_Qcross", markdown)
        self.assertIn("Fit to observations: False", markdown)
        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Compatibility closes: False", markdown)


if __name__ == "__main__":
    unittest.main()
