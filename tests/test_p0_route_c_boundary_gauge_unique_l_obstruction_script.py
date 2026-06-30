from __future__ import annotations

import unittest

from scripts.build_p0_route_c_boundary_gauge_unique_l_obstruction import (
    build_payload,
    render_markdown,
)


class P0RouteCBoundaryGaugeUniqueLObstructionTests(unittest.TestCase):
    def test_boundary_gauge_does_not_select_zero_axiom_l(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "boundary-gauge-unique-l-obstruction-open")
        self.assertTrue(payload["strong_boundary_selectors_exist"])
        self.assertFalse(payload["strong_boundary_selectors_source_supplied"])
        self.assertTrue(payload["structural_mirror_boundary_insufficient"])
        self.assertFalse(payload["unique_l_from_boundary_gauge"])
        self.assertTrue(payload["new_boundary_axiom_required_if_adopted"])
        self.assertFalse(payload["flrw_background_promotion_allowed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_distinguish_strong_and_structural_selectors(self) -> None:
        rows = {row["selector"]: row for row in build_payload()["rows"]}

        self.assertTrue(rows["pointwise_identity_gauge"]["can_fix_l"])
        self.assertTrue(rows["unit_jacobian_or_tetrad_basepoint"]["can_fix_l"])
        self.assertFalse(rows["mirror_inverse_boundary"]["can_fix_l"])
        self.assertFalse(rows["periodic_topology"]["can_fix_l"])

    def test_markdown_reports_boundary_axiom(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Boundary/Gauge Unique-L", markdown)
        self.assertIn("New boundary axiom required if adopted: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
