from __future__ import annotations

import unittest

from scripts.build_p0_local_low_derivative_scouple_restricted_no_go import (
    build_payload,
    render_markdown,
)


class P0LocalLowDerivativeScoupleRestrictedNoGoTests(unittest.TestCase):
    def test_restricted_no_go_is_proved_but_full_no_go_is_not(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "restricted-local-low-derivative-scouple-no-go-proved")
        self.assertTrue(payload["restricted_no_go_proved"])
        self.assertFalse(payload["full_local_low_derivative_no_go_proved"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_obstruction_rows_all_close_inside_restricted_class(self) -> None:
        payload = build_payload()
        rows = {row["obstruction"]: row for row in payload["obstruction_rows"]}

        self.assertTrue(all(row["closed"] for row in payload["obstruction_rows"]))
        self.assertIn("pure_pullback_identity", rows)
        self.assertIn("b4vol_product_degeneracy", rows)
        self.assertIn("ultralocal_metric_invariant_family", rows)
        self.assertIn("no_l_transport_from_ultralocal_l", rows)
        self.assertIn("matter_scalar_family_open", rows)
        self.assertIn("single_noether_rank_one", rows)

    def test_each_easy_selector_remains_false(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["pure_pullback_selects_phi_j_l"])
        self.assertFalse(payload["metric_invariant_unique_phi_forced"])
        self.assertFalse(payload["metric_invariant_el_is_transport"])
        self.assertFalse(payload["matter_invariant_unique"])
        self.assertFalse(payload["split_noether_closes_two_residuals"])
        self.assertFalse(payload["b4vol_alone_selects_jphi"])

    def test_zero_rustine_and_exclusions_are_explicit(self) -> None:
        payload = build_payload()
        exclusions = " ".join(payload["exclusions"])

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["hidden_axiom_used"])
        self.assertIn("higher-derivative", exclusions)
        self.assertIn("nonlocal", exclusions)
        self.assertIn("source-derived actions", exclusions)

    def test_markdown_reports_scope(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Restricted no-go proved: True", markdown)
        self.assertIn("Full local low-derivative no-go proved: False", markdown)
        self.assertIn("pure_pullback_identity", markdown)
        self.assertIn("This is not a full no-go theorem", markdown)


if __name__ == "__main__":
    unittest.main()
