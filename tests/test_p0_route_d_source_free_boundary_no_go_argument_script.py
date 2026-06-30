from __future__ import annotations

import unittest

from scripts.build_p0_route_d_source_free_boundary_no_go_argument import (
    build_payload,
    render_markdown,
)


class P0RouteDSourceFreeBoundaryNoGoArgumentTests(unittest.TestCase):
    def test_bounded_no_go_is_proved_without_full_no_go_claim(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-free-boundary-no-go-argument-bounded")
        self.assertTrue(payload["proved_for_source_free_boundary_free_local_pde"])
        self.assertTrue(payload["periodic_kernel_detected"])
        self.assertTrue(payload["boundary_selectors_can_fix_but_unsourced"])
        self.assertFalse(payload["principal_symbol_sufficient"])
        self.assertTrue(payload["source_derived_operator_still_open"])
        self.assertFalse(payload["full_no_go_proved"])
        self.assertFalse(payload["prediction_ready"])

    def test_excluded_and_open_scopes_are_distinct(self) -> None:
        payload = build_payload()
        excluded = " ".join(payload["excluded_scope"])
        open_scope = " ".join(payload["open_scope"])

        self.assertIn("source-free", excluded)
        self.assertIn("boundary-selected", excluded)
        self.assertIn("source-derived STF", open_scope)
        self.assertIn("same-L Noether", open_scope)

    def test_markdown_reports_bounded_no_go(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("No-Go Argument", markdown)
        self.assertIn("Full no-go proved: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
