from __future__ import annotations

import unittest

from scripts.build_p0_janus_weak_selector_action_origin_audit import (
    build_payload,
    render_markdown,
)


class P0JanusWeakSelectorActionOriginAuditTests(unittest.TestCase):
    def test_active_cross_action_derives_selector_but_source_acceptance_open(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "active-cross-action-derives-selector-source-acceptance-open",
        )
        self.assertTrue(payload["passive_pullback_insufficient"])
        self.assertTrue(payload["active_cross_dust_action_derives_weak_selector"])
        self.assertTrue(payload["weak_selector_derivation_shape_closed"])
        self.assertFalse(payload["active_cross_action_source_accepted"])
        self.assertEqual(
            payload["active_cross_action_acceptance_artifact"],
            "p0_janus_active_cross_action_acceptance_gate",
        )
        self.assertTrue(payload["multiplier_route_rejected_as_rustine"])
        self.assertFalse(payload["weak_selector_action_origin_closed"])
        self.assertTrue(payload["new_axiom_if_adopted_without_janus_source"])
        self.assertFalse(payload["prediction_ready"])

    def test_action_rows_distinguish_passive_active_and_multiplier(self) -> None:
        rows = {row["action"]: row for row in build_payload()["action_rows"]}

        self.assertFalse(rows["passive_source_dust_pullback"]["derives_weak_selector"])
        self.assertTrue(rows["active_receiver_cross_dust"]["derives_weak_selector"])
        self.assertTrue(rows["weak_congruence_multiplier"]["derives_weak_selector"])
        self.assertFalse(rows["weak_congruence_multiplier"]["accepted_without_new_axiom"])

    def test_derivation_rows_close_shape_but_not_janus_acceptance(self) -> None:
        rows = {row["row"]: row for row in build_payload()["derivation_rows"]}

        self.assertTrue(rows["diffeomorphism_variation"]["closed"])
        self.assertTrue(rows["dust_stress"]["closed"])
        self.assertTrue(rows["continuity_split"]["closed"])
        self.assertTrue(rows["projected_el"]["closed"])
        self.assertFalse(rows["janus_source_acceptance"]["closed"])
        self.assertIn("h^alpha_nu", rows["projected_el"]["formula"])

    def test_no_fit_or_absorption(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["requires_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["physics_closed"])

    def test_markdown_reports_open_action_origin(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Weak Selector Action Origin", markdown)
        self.assertIn("Active cross dust action derives weak selector: True", markdown)
        self.assertIn("Active cross action source accepted: False", markdown)
        self.assertIn("Active cross action acceptance artifact", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
