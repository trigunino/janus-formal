from __future__ import annotations

import unittest

from scripts.build_p0_lorentz_tetrad_selector_obstruction import (
    build_payload,
    render_markdown,
)


class P0LorentzTetradSelectorObstructionTests(unittest.TestCase):
    def test_lorentz_boost_family_is_symbolically_admissible(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "lorentz-tetrad-selector-obstruction-open")
        self.assertTrue(payload["lorentz_condition_symbolically_closed"])
        self.assertTrue(payload["proper_boost_determinant_fixed"])
        self.assertTrue(payload["rapidity_family_remains_free"])

    def test_lorentz_condition_does_not_select_l_or_jphi(self) -> None:
        payload = build_payload()
        rows = {row["condition"]: row for row in payload["rows"]}

        self.assertFalse(payload["lorentz_admissibility_selects_unique_l"])
        self.assertFalse(payload["lorentz_admissibility_selects_jphi"])
        self.assertTrue(payload["requires_source_rapidity_transport"])
        self.assertTrue(payload["requires_same_l_transport_proof"])
        self.assertFalse(rows["lorentz_admissibility"]["selects_unique_l"])
        self.assertFalse(rows["determinant"]["selects_unique_l"])

    def test_no_rustine_shortcuts_are_used(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["hidden_axiom_used"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_obstruction(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Rapidity family remains free: True", markdown)
        self.assertIn("Lorentz admissibility selects J_phi: False", markdown)
        self.assertIn("Requires source rapidity transport: True", markdown)
        self.assertIn("same-L transport", markdown)


if __name__ == "__main__":
    unittest.main()
