from __future__ import annotations

import unittest

from scripts.build_p0_janus_next_work_organization_review import (
    build_payload,
    render_markdown,
)


class P0JanusNextWorkOrganizationReviewTests(unittest.TestCase):
    def test_review_states_current_gap_and_nonpredictive_status(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "organized-next-work-index-ready")
        self.assertTrue(payload["active_cross_action_math_valid"])
        self.assertFalse(payload["active_cross_action_source_accepted"])
        self.assertTrue(payload["no_axiom_exhaustion_program_available"])
        self.assertTrue(payload["generic_metric_isometry_rejected"])
        self.assertTrue(payload["weak_dust_target_reached"])
        self.assertFalse(payload["all_source_items_derived"])
        self.assertFalse(payload["new_axiom_adopted"])
        self.assertFalse(payload["prediction_ready"])

    def test_missing_core_names_real_model_gaps(self) -> None:
        missing = " ".join(row["missing"] for row in build_payload()["missing_core"])

        self.assertIn("S_x/S_couple", missing)
        self.assertIn("mirror", missing)
        self.assertIn("same-L/DL", missing)
        self.assertIn("B4vol", missing)
        self.assertIn("non-dust", missing)

    def test_decision_tree_has_source_axiom_and_no_axiom_routes(self) -> None:
        routes = {row["route"] for row in build_payload()["decision_tree"]}

        self.assertEqual(routes, {"find_source", "new_axiom", "no_new_axiom"})

    def test_markdown_is_practical_index(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Next Work Organization", markdown)
        self.assertIn("Organization Layers", markdown)
        self.assertIn("Missing Core", markdown)
        self.assertIn("No-axiom exhaustion program available: True", markdown)
        self.assertIn("Recommended Next", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
