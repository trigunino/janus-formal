from __future__ import annotations

import unittest

from scripts.build_p0_route_c_action_noether_path_rule_derivation_attempt import (
    build_payload,
    render_markdown,
)


class P0RouteCActionNoetherPathRuleDerivationAttemptTests(unittest.TestCase):
    def test_action_noether_attempt_is_obstructed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "action-noether-path-rule-derivation-attempt-obstructed")
        self.assertFalse(payload["indirect_source_found"])
        self.assertTrue(payload["underselection_bounded_no_go_closed"])
        self.assertEqual(payload["accepted_zero_axiom_derivation_count"], 0)
        self.assertFalse(payload["action_noether_path_rule_derived"])
        self.assertTrue(payload["noether_derives_constraints_not_selector"])
        self.assertTrue(payload["wilson_line_action_is_possible_extension"])
        self.assertFalse(payload["wilson_line_action_adopted"])
        self.assertTrue(payload["new_axiom_if_wilson_line_adopted"])
        self.assertFalse(payload["prediction_ready"])

    def test_attempt_rows_cover_noether_geodesic_bf_wilson_and_matter(self) -> None:
        routes = {row["route"] for row in build_payload()["rows"]}

        self.assertEqual(
            routes,
            {
                "diffeomorphism_noether",
                "worldline_geodesic_action",
                "reparametrization_noether",
                "bf_connection_noether",
                "wilson_line_path_action",
                "matter_pullback_action",
            },
        )

    def test_markdown_reports_wilson_extension_risk(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Action/Noether Path-Rule", markdown)
        self.assertIn("Wilson-line action adopted: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
