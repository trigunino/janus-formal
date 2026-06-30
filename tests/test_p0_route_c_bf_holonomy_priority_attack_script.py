from __future__ import annotations

import unittest

from scripts.build_p0_route_c_bf_holonomy_priority_attack import build_payload, render_markdown


class P0RouteCBFHolonomyPriorityAttackTests(unittest.TestCase):
    def test_priority_attack_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "bf-holonomy-priority-attack-open")
        self.assertTrue(payload["bf_same_l_for_k_qcross"])
        self.assertFalse(payload["holonomy_source_derived"])
        self.assertFalse(payload["phi_r_free_insert_allowed"])
        self.assertTrue(payload["curvature_identity_available"])
        self.assertTrue(payload["weakfield_phi_r_candidate_available"])
        self.assertFalse(payload["phi_r_source_derived"])
        self.assertFalse(payload["path_rule_source_derived"])
        self.assertFalse(payload["same_l_transport_proved"])
        self.assertFalse(payload["l_uniquely_selected"])
        self.assertTrue(payload["strongest_no_axiom_candidate"])
        self.assertTrue(payload["new_axiom_risk"])
        self.assertFalse(payload["prediction_ready"])

    def test_attack_rows_cover_source_curvature_transport_holonomy_and_same_l(self) -> None:
        targets = {row["target"] for row in build_payload()["attack_rows"]}

        self.assertEqual(targets, {"source_curvature", "transport", "holonomy", "same_l_residual"})

    def test_markdown_reports_bf_holonomy(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("BF/Holonomy", markdown)
        self.assertIn("Phi_R source derived: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
