from __future__ import annotations

import unittest

from scripts.build_p0_b4vol_jacobian_gauge_degeneracy_proof import (
    build_payload,
    render_markdown,
)


class P0B4volJacobianGaugeDegeneracyProofTests(unittest.TestCase):
    def test_product_and_dlog_degeneracy_are_symbolically_closed(self) -> None:
        payload = build_payload()
        rows = {row["identity"]: row for row in payload["rows"]}

        self.assertEqual(payload["status"], "b4vol-jacobian-gauge-degeneracy-proved")
        self.assertTrue(payload["degeneracy_symbolic_identity_closed"])
        self.assertTrue(rows["multiplicative_gauge_family"]["closed"])
        self.assertTrue(rows["dlog_family"]["closed"])

    def test_b4vol_alone_does_not_select_jphi(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["source_b4vol_alone_selects_jphi"])
        self.assertTrue(payload["requires_slice_lapse_selector"])
        self.assertTrue(payload["flrw_fixed_slice_conditional_selects_jphi"])
        self.assertFalse(payload["general_perturbed_jphi_selected"])

    def test_not_a_prediction_or_fit_shortcut(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_keeps_gauge_degeneracy_visible(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("J_phi -> exp(lambda) J_phi", markdown)
        self.assertIn("Source B4vol alone selects J_phi: False", markdown)
        self.assertIn("Requires slice/lapse selector: True", markdown)
        self.assertIn("General perturbed J_phi selected: False", markdown)


if __name__ == "__main__":
    unittest.main()
