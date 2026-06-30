from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_map_equation_connection_compatibility import (
    build_payload,
    render_markdown,
)


class P0StueckelbergMapEquationConnectionCompatibilityTests(unittest.TestCase):
    def test_artifact_is_conditional_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "connection-compatibility-conditional-open")
        self.assertFalse(payload["source_derived"])
        self.assertTrue(payload["new_axiom"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["fit_to_observations"])

    def test_equations_cancel_connection_differences_in_both_residuals(self) -> None:
        equations = " ".join(
            row["id"] + " " + row["equation"] + " " + row["role"]
            for row in build_payload()["compatibility_equations"]
        )

        self.assertIn("E_phi_plus", equations)
        self.assertIn("E_L_plus", equations)
        self.assertIn("E_phi_minus", equations)
        self.assertIn("E_L_minus", equations)
        self.assertIn("DeltaGamma", equations)
        self.assertIn("Deltaomega", equations)
        self.assertIn("R_plus", equations)
        self.assertIn("R_minus", equations)

    def test_checks_include_integrability_overconstraint_mirror_and_no_fit(self) -> None:
        checks = {row["name"]: row for row in build_payload()["checks"]}

        self.assertIn("integrability", checks)
        self.assertIn("overconstraint", checks)
        self.assertIn("mirror_sector_consistency", checks)
        self.assertIn("no_fit", checks)
        self.assertIn("curl", checks["integrability"]["requirement"])
        self.assertEqual(checks["overconstraint"]["status"], "likely-overconstrained")
        self.assertIn("phi^{-1}, L^{-1}", checks["mirror_sector_consistency"]["requirement"])
        self.assertEqual(checks["no_fit"]["status"], "enforced-by-branch")

    def test_closure_decision_is_false_but_conditional(self) -> None:
        decision = build_payload()["closure_decision"]

        self.assertFalse(decision["compatibility_closes"])
        self.assertTrue(decision["conditional_closure_possible"])
        self.assertIn("integrability", decision["reason"])
        self.assertIn("overconstrained", " ".join(decision["required_for_closure"]))

    def test_markdown_reports_prediction_and_closure_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Fit to observations: False", markdown)
        self.assertIn("Compatibility closes: False", markdown)
        self.assertIn("mirror consistency", markdown)


if __name__ == "__main__":
    unittest.main()
