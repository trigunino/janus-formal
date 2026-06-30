from __future__ import annotations

import unittest

from scripts.build_p0_holonomy_path_rule_branch import build_payload, render_markdown


class P0HolonomyPathRuleBranchTests(unittest.TestCase):
    def test_artifact_is_broad_pass_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "broad-pass-research-artifact")
        self.assertFalse(payload["source_derived"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertTrue(payload["not_predictive"])

    def test_premise_requires_path_dependence_and_same_rule(self) -> None:
        premise = " ".join(build_payload()["premise"])

        self.assertIn("R_Omega != 0", premise)
        self.assertIn("chosen path or path family", premise)
        self.assertIn("K and Q_cross must use the same path/family rule", premise)

    def test_lists_required_candidate_path_rules(self) -> None:
        names = {rule["name"] for rule in build_payload()["candidate_path_rules"]}

        self.assertEqual(
            names,
            {
                "positive_null_ray",
                "matter_worldline",
                "geodesic_congruence",
                "hypersurface_normal",
            },
        )

    def test_each_rule_has_source_loop_and_no_fit_constraints(self) -> None:
        for rule in build_payload()["candidate_path_rules"]:
            self.assertTrue(rule["source_requirements"])
            self.assertIn("loop", rule["loop_consistency"].lower())
            self.assertTrue(rule["no_fit_constraints"])

    def test_required_checks_keep_branch_source_derived_and_unfitted(self) -> None:
        checks = " ".join(build_payload()["required_checks"])

        self.assertIn("Janus sources", checks)
        self.assertIn("identical path/family rule for K and Q_cross", checks)
        self.assertIn("loop consistency", checks)
        self.assertIn("survey residuals", checks)

    def test_markdown_renders_guardrails(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Source requirements", markdown)
        self.assertIn("No-fit constraints", markdown)
        self.assertIn("same rule is used for K and Q_cross", markdown)


if __name__ == "__main__":
    unittest.main()
