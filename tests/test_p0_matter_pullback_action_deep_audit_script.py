from __future__ import annotations

import unittest

from scripts.build_p0_matter_pullback_action_deep_audit import (
    build_payload,
    render_markdown,
)


class P0MatterPullbackActionDeepAuditTests(unittest.TestCase):
    def test_pure_pullback_is_identity_not_selector(self) -> None:
        payload = build_payload()
        rows = {row["route"]: row for row in payload["rows"]}

        self.assertEqual(payload["status"], "matter-pullback-action-deep-audit-selector-open")
        self.assertTrue(payload["pure_pullback_euler_lagrange_zero"])
        self.assertEqual(payload["pure_pullback_el_operator"], "0")
        self.assertFalse(payload["pure_matter_pullback_selects_phi_j_l"])
        self.assertFalse(rows["pure_top_form_pullback"]["selects_phi_j_l"])

    def test_projected_dust_shape_is_progress_but_conditional(self) -> None:
        payload = build_payload()
        rows = {row["route"]: row for row in payload["rows"]}

        self.assertTrue(payload["projected_dust_force_shape_derived"])
        self.assertTrue(payload["projected_dust_force_shape_conditional"])
        self.assertFalse(rows["projected_dust_variation"]["selects_phi_j_l"])
        self.assertFalse(payload["same_phi_l_selection_derived"])
        self.assertTrue(payload["janus_specific_action_still_required"])

    def test_receiver_weighted_term_is_true_coupling_not_pure_pullback(self) -> None:
        payload = build_payload()

        self.assertIn("Derivative(W(x), x)", payload["weighted_pullback_el_operator"])
        self.assertTrue(payload["receiver_weighted_term_is_scouple_not_pure_pullback"])
        self.assertFalse(payload["pressure_pi_extension_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_zero_rustine_guards_and_markdown(self) -> None:
        payload = build_payload()
        markdown = render_markdown(payload)

        self.assertTrue(payload["deep_action_pullback_attempt_completed"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["hidden_axiom_used"])
        self.assertIn("Pure matter pullback selects phi/J/L: False", markdown)
        self.assertIn("Janus-specific action still required: True", markdown)
        self.assertIn("convert the route into a bounded no-go theorem", markdown)


if __name__ == "__main__":
    unittest.main()
