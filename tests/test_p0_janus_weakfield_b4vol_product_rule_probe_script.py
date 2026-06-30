from __future__ import annotations

import unittest

from scripts.build_p0_janus_weakfield_b4vol_product_rule_probe import build_payload, render_markdown


class P0JanusWeakfieldB4volProductRuleProbeScriptTests(unittest.TestCase):
    def test_linear_product_rule_matches_without_qdet_absorption(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["linear_product_rule_matches"])
        self.assertTrue(payload["b4vol_1p1_computed"])
        self.assertFalse(payload["b4vol_source_law_derived"])
        self.assertFalse(payload["qdet_absorbed"])

    def test_no_prediction_claim(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_boundary(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("B4vol source law derived: False", markdown)
        self.assertIn("does not derive the Janus 4D B4vol source law", markdown)


if __name__ == "__main__":
    unittest.main()
