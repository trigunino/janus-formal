from __future__ import annotations

import unittest

from scripts.build_p0_janus_active_cross_action_acceptance_gate import (
    build_payload,
    render_markdown,
)


class P0JanusActiveCrossActionAcceptanceGateTests(unittest.TestCase):
    def test_active_action_is_math_valid_but_not_source_accepted(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "active-cross-action-math-valid-source-not-accepted")
        self.assertTrue(payload["m15_field_equation_action_available"])
        self.assertFalse(payload["m15_accepted_as_scouple"])
        self.assertFalse(payload["independent_scouple_found"])
        self.assertFalse(payload["external_variational_transport_law_found"])
        self.assertTrue(payload["active_cross_action_derives_weak_selector"])
        self.assertFalse(payload["active_cross_action_source_accepted"])
        self.assertTrue(payload["source_material"]["M15_source_card_exists"])
        self.assertTrue(payload["source_material"]["M30_source_card_exists"])
        self.assertFalse(payload["source_material_sufficient_for_reaudit"])
        self.assertEqual(
            payload["next_research_step"],
            "acquire_or_restore_M15_M30_raw_sources_then_reaudit_S_cross",
        )
        self.assertFalse(payload["can_adopt_as_published_janus"])
        self.assertTrue(payload["can_adopt_as_explicit_new_axiom"])
        self.assertFalse(payload["new_axiom_adopted"])
        self.assertFalse(payload["prediction_ready"])

    def test_acceptance_rows_separate_field_source_from_phi_l_variation(self) -> None:
        rows = {row["check"]: row for row in build_payload()["acceptance_rows"]}

        self.assertTrue(rows["field_equation_source_slot"]["available"])
        self.assertFalse(rows["field_equation_source_slot"]["accepts_active_action"])
        self.assertFalse(rows["independent_scouple"]["available"])
        self.assertFalse(rows["map_variation"]["available"])
        self.assertEqual(rows["weak_selector_shape"]["accepts_active_action"], "math-shape-only")
        self.assertTrue(rows["no_rustine"]["available"])

    def test_no_fit_or_scalar_absorption(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["requires_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["physics_closed"])

    def test_markdown_reports_axiom_boundary(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Active Cross Action Acceptance", markdown)
        self.assertIn("Can adopt as published Janus: False", markdown)
        self.assertIn("Can adopt as explicit new axiom: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
