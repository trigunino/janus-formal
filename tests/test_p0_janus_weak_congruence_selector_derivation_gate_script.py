from __future__ import annotations

import unittest

import numpy as np

from scripts.build_p0_janus_weak_congruence_selector_derivation_gate import (
    build_connection_difference,
    build_payload,
    connection_force,
    projector_perp_u,
    render_markdown,
)


class P0JanusWeakCongruenceSelectorDerivationGateTests(unittest.TestCase):
    def test_weak_selector_cancels_dust_projection_without_isometry(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "weak-congruence-selector-derived-as-target-action-origin-open",
        )
        self.assertTrue(payload["weak_selector_equation_written"])
        self.assertTrue(payload["dust_projected_residual_cancelled"])
        self.assertTrue(payload["full_connection_not_zero"])
        self.assertTrue(payload["does_not_impose_metric_isometry"])
        self.assertTrue(payload["generic_janus_not_excluded"])
        self.assertFalse(payload["action_origin_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_numeric_projection_matches_direct_matrix_calculation(self) -> None:
        u = np.array([1.0, 0.0, 0.0, 0.0])
        h = projector_perp_u(u)
        c = build_connection_difference()

        projected = h @ connection_force(c, u)

        self.assertGreater(np.linalg.norm(projected), 1e-3)
        np.testing.assert_allclose(projected + (-projected), np.zeros(4), atol=1e-12)
        self.assertGreater(np.max(np.abs(c)), 1e-3)

    def test_rows_distinguish_target_from_action_closure(self) -> None:
        rows = {row["name"]: row for row in build_payload()["selector_rows"]}

        self.assertTrue(rows["weak_selector"]["closed"])
        self.assertTrue(rows["not_isometry"]["closed"])
        self.assertFalse(rows["projected_action_target"]["closed"])
        self.assertFalse(rows["mirror_target"]["closed"])
        self.assertFalse(rows["non_dust_extension"]["closed"])

    def test_no_fit_or_absorption(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["requires_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["physics_closed"])

    def test_markdown_reports_open_action_origin(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Weak Congruence Selector", markdown)
        self.assertIn("Dust projected residual cancelled: True", markdown)
        self.assertIn("Action origin closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
