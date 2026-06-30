from __future__ import annotations

import unittest

from scripts.build_p0_route_d_stf_no_go_closure_attempt import build_payload, render_markdown


class P0RouteDSTFNoGoClosureAttemptTests(unittest.TestCase):
    def test_stf_no_go_closes_known_non_source_families_only(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "stf-no-go-closure-attempt-partial")
        self.assertEqual(payload["closed_family_count"], 4)
        self.assertEqual(payload["open_family_count"], 1)
        self.assertFalse(payload["accepted_janus_derived_stf_operator_exists"])
        self.assertTrue(payload["all_known_non_source_stf_families_excluded"])
        self.assertFalse(payload["full_stf_no_go_proved"])
        self.assertEqual(payload["logical_escape_remaining"], "accepted_janus_source_derived_stf_operator")
        self.assertFalse(payload["new_axiom_adopted"])
        self.assertFalse(payload["prediction_ready"])

    def test_only_source_derived_family_remains_open(self) -> None:
        open_rows = [row for row in build_payload()["closure_rows"] if not row["closed_no_go"]]

        self.assertEqual(len(open_rows), 1)
        self.assertEqual(open_rows[0]["family"], "accepted_janus_source_derived_stf_operator")

    def test_markdown_reports_partial_no_go(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("STF No-Go Closure Attempt", markdown)
        self.assertIn("Full STF no-go proved: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
