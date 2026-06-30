from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_map_integrability_curl_conditions import (
    build_payload,
    render_markdown,
)


class P0StueckelbergMapIntegrabilityCurlConditionsTests(unittest.TestCase):
    def test_artifact_is_conditional_open_and_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "map-integrability-curl-conditional-open")
        self.assertFalse(payload["source_derived"])
        self.assertTrue(payload["new_axiom"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["fit_to_observations"])
        self.assertEqual(payload["free_parameters"], [])

    def test_map_equations_cover_e_phi_e_l_plus_minus_cancellations(self) -> None:
        equations = " ".join(
            row["id"] + " " + row["equation"] + " " + row["cancels"] + " " + row["curl_condition"]
            for row in build_payload()["map_equations"]
        )

        self.assertIn("E_phi_plus", equations)
        self.assertIn("E_L_plus", equations)
        self.assertIn("E_phi_minus", equations)
        self.assertIn("E_L_minus", equations)
        self.assertIn("DeltaGamma", equations)
        self.assertIn("Deltaomega", equations)
        self.assertIn("R_plus", equations)
        self.assertIn("R_minus", equations)
        self.assertIn("D_plus_[mu", equations)
        self.assertIn("D_minus_[a", equations)

    def test_curl_tests_are_frobenius_like_and_conditionally_nonzero(self) -> None:
        tests = {row["name"]: row for row in build_payload()["curl_tests"]}

        self.assertIn("phi_plus_frobenius", tests)
        self.assertIn("L_plus_frobenius", tests)
        self.assertIn("phi_minus_frobenius", tests)
        self.assertIn("L_minus_frobenius", tests)
        self.assertTrue(all(row["vanishes"] == "conditional" for row in tests.values()))
        self.assertIn("curvature", tests["phi_plus_frobenius"]["expected_form"])
        self.assertIn("Lorentz curvature", tests["L_plus_frobenius"]["expected_form"])
        self.assertIn("mirror", tests["phi_minus_frobenius"]["expected_form"])
        self.assertIn("mirror", tests["L_minus_frobenius"]["expected_form"])

    def test_consistency_conditions_include_obstruction_mirror_and_no_fit(self) -> None:
        conditions = {row["name"]: row for row in build_payload()["consistency_conditions"]}

        self.assertIn("frobenius_like_closure", conditions)
        self.assertIn("curvature_obstruction", conditions)
        self.assertIn("mirror_consistency", conditions)
        self.assertIn("no_fit", conditions)
        self.assertEqual(conditions["curvature_obstruction"]["status"], "open-obstruction")
        self.assertIn("phi^{-1}, L^{-1}", conditions["mirror_consistency"]["condition"])
        self.assertEqual(conditions["no_fit"]["status"], "enforced-by-branch")

    def test_closure_decision_blocks_unconditional_curl_vanishing(self) -> None:
        decision = build_payload()["closure_decision"]

        self.assertEqual(decision["curls_vanish"], "conditional")
        self.assertTrue(decision["curls_vanish_false_unconditionally"])
        self.assertFalse(decision["integrability_closes"])
        self.assertTrue(decision["conditional_closure_possible"])
        self.assertIn("curvature", decision["reason"])
        self.assertIn("without fit", " ".join(decision["required_for_closure"]))
        self.assertIn("mirror", " ".join(decision["required_for_closure"]))

    def test_markdown_reports_curl_status_and_prediction_block(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Fit to observations: False", markdown)
        self.assertIn("Curls vanish: conditional", markdown)
        self.assertIn("Curls vanish false unconditionally: True", markdown)
        self.assertIn("Integrability closes: False", markdown)
        self.assertIn("curvature obstruction", markdown)


if __name__ == "__main__":
    unittest.main()
