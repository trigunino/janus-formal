from __future__ import annotations

import unittest

from scripts.build_p0_janus_pulled_dust_action_weak_congruence_proof import (
    build_payload,
    render_markdown,
)


class P0JanusPulledDustActionWeakCongruenceProofTests(unittest.TestCase):
    def test_dust_chain_reaches_target_but_not_full_closure(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "pulled-dust-action-proof-conditional-action-origin-open",
        )
        self.assertTrue(payload["standard_dust_variation_closed"])
        self.assertTrue(payload["single_cross_pullback_dust_closed"])
        self.assertTrue(payload["projected_cuu_target_reached"])
        self.assertEqual(
            payload["weak_selector_action_origin_artifact"],
            "p0_janus_weak_selector_action_origin_audit",
        )
        self.assertTrue(payload["active_cross_dust_action_derives_weak_selector"])
        self.assertFalse(payload["action_origin_for_weak_selector_closed"])
        self.assertTrue(payload["new_axiom_if_adopted_without_janus_source"])
        self.assertFalse(payload["mirror_inverse_closed"])
        self.assertFalse(payload["pressure_pi_extension_closed"])
        self.assertFalse(payload["conditional_dust_closure_ready"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_keep_closed_and_open_parts_separate(self) -> None:
        payload = build_payload()
        rows = {row["row"]: row for row in payload["proof_rows"]}

        self.assertTrue(rows["particle_to_geodesic"]["closed"])
        self.assertTrue(rows["cold_dust_lift"]["closed"])
        self.assertTrue(rows["pullback_continuity"]["closed"])
        self.assertTrue(rows["projected_connection_difference"]["closed"])
        self.assertTrue(rows["weak_congruence_target"]["closed"])
        self.assertFalse(rows["action_origin_for_selector"]["closed"])
        self.assertFalse(rows["mirror_inverse"]["closed"])
        self.assertFalse(rows["pressure_pi_extension"]["closed"])
        self.assertIn("action_origin_for_selector", payload["open_rows"])

    def test_no_fit_or_absorption(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["requires_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["physics_closed"])

    def test_markdown_reports_conditional_action_origin(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Pulled Dust Action Weak Congruence Proof", markdown)
        self.assertIn("Projected Cuu target reached: True", markdown)
        self.assertIn("Active cross dust action derives weak selector: True", markdown)
        self.assertIn("Action origin for weak selector closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
