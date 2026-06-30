from __future__ import annotations

import unittest

from scripts.build_p0_route_c_pt_selector_derivation_attempt import (
    build_payload,
    render_markdown,
)


class P0RouteCPtSelectorDerivationAttemptTests(unittest.TestCase):
    def test_pt_selector_attempt_formalizes_but_does_not_close(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "pt-selector-derivation-attempt-open")
        self.assertTrue(payload["pt_geometry_formalized"])
        self.assertTrue(payload["pt_surface_family_underselected"])
        self.assertTrue(payload["identity_holonomy_cost_tie"])
        self.assertTrue(payload["two_path_counterexample_active"])
        self.assertFalse(payload["zero_axiom_pt_selector_found"])
        self.assertTrue(payload["requires_new_source_term_or_axiom"])
        self.assertFalse(payload["prediction_ready"])

    def test_three_candidate_routes_are_tested_and_all_remain_open(self) -> None:
        rows = {row["candidate"]: row for row in build_payload()["candidate_rows"]}

        self.assertEqual(
            set(rows),
            {
                "pt_fixed_surface",
                "pt_path_functional",
                "pt_holonomy_minimal_curvature",
            },
        )
        self.assertTrue(all(row["pt_condition_passes"] for row in rows.values()))
        self.assertTrue(all(not row["selector_derived"] for row in rows.values()))

    def test_same_l_stack_and_surface_counterexample_are_explicit(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["surface_a_pt_odd_residual"], "0")
        self.assertEqual(payload["surface_b_pt_odd_residual"], "0")
        self.assertEqual(payload["same_l_required_for"], ["K", "Q_cross", "Vlasov/matter", "mirror_inverse"])

    def test_markdown_reports_no_pt_selector(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("PT Selector Derivation Attempt", markdown)
        self.assertIn("Zero-axiom PT selector found: False", markdown)
        self.assertIn("Requires new source term or axiom: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
