from __future__ import annotations

import unittest

from scripts.build_p0_route_c_pt_only_no_selector_certificate import (
    build_payload,
    render_markdown,
)


class P0RouteCPtOnlyNoSelectorCertificateTests(unittest.TestCase):
    def test_pt_only_no_selector_is_bounded_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "pt-only-no-selector-certificate-bounded")
        self.assertTrue(payload["bounded_pt_only_no_selector_closed"])
        self.assertFalse(payload["pt_only_selects_unique_l"])
        self.assertTrue(payload["ordered_path_action_is_escape"])
        self.assertTrue(payload["requires_janus_source_for_escape"])
        self.assertFalse(payload["prediction_ready"])

    def test_pt_parity_families_are_underselected(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["pt_odd_surface_residual"], "0")
        self.assertEqual(payload["pt_even_cost_residual"], "0")
        self.assertEqual(payload["pt_surface_family_dimension_tested"], 3)
        self.assertEqual(payload["pt_cost_family_dimension_tested"], 3)

    def test_scalar_invariants_tie_while_l_differs(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["scalar_invariants_tie"])
        self.assertGreater(payload["frobenius_l_difference_xy_yx"], 0.0)
        self.assertTrue(payload["noncommuting_paths_select_different_l"])

    def test_markdown_reports_escape_condition(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("PT-Only No-Selector Certificate", markdown)
        self.assertIn("PT-only selects unique L: False", markdown)
        self.assertIn("Requires Janus source for escape: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
