from __future__ import annotations

import unittest

from scripts.build_p0_phi_j_l_boundary_selector_probe import build_payload, render_markdown


class P0PhiJLBoundarySelectorProbeTests(unittest.TestCase):
    def test_strong_selectors_exist_but_are_not_source_supplied(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "boundary-selectors-can-fix-family-but-not-source-supplied",
        )
        self.assertTrue(payload["strong_selectors_exist"])
        self.assertFalse(payload["strong_selectors_source_supplied"])
        self.assertTrue(payload["new_boundary_axiom_required_if_adopted"])
        self.assertFalse(payload["prediction_ready"])

    def test_structural_conditions_do_not_fix_unique_map(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["mirror_topology_alone_fixes_unique_map"])
        self.assertFalse(payload["periodic_boundary_alone_fixes_unique_map"])
        self.assertFalse(payload["physics_closed"])

    def test_selector_rows_distinguish_strong_and_structural(self) -> None:
        rows = {row["selector"]: row for row in build_payload()["selectors"]}

        self.assertTrue(rows["identity_at_quarter_turn"]["fixes_epsilon"])
        self.assertTrue(rows["unit_jacobian_at_origin"]["fixes_epsilon"])
        self.assertFalse(rows["periodic_endpoints"]["fixes_epsilon"])
        self.assertFalse(rows["mirror_inverse_only"]["fixes_epsilon"])
        self.assertFalse(rows["identity_at_quarter_turn"]["source_supplied"])
        self.assertTrue(rows["periodic_endpoints"]["source_supplied"])

    def test_no_observational_fit(self) -> None:
        self.assertFalse(build_payload()["uses_observational_fit"])

    def test_markdown_keeps_boundary_axiom_warning(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Strong selectors source supplied: False", markdown)
        self.assertIn("New boundary axiom required if adopted: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
