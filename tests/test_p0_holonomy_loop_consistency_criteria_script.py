from __future__ import annotations

import unittest

from scripts.build_p0_holonomy_loop_consistency_criteria import (
    build_payload,
    render_markdown,
)


class P0HolonomyLoopConsistencyCriteriaTests(unittest.TestCase):
    def test_artifact_is_bounded_open_and_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "criteria-open")
        self.assertTrue(payload["nonflat_relative_connection"])
        self.assertFalse(payload["source_derived"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_required_holonomy_criteria_are_present(self) -> None:
        criteria = " ".join(
            f"{row['criterion']} {row['accept']}" for row in build_payload()["criteria"]
        )

        self.assertIn("R_Omega != 0", criteria)
        self.assertIn("path choice must be source-derived", criteria)
        self.assertIn("closed source-receiver loops", criteria)
        self.assertIn("subdividing the same declared path/family", criteria)
        self.assertIn("same source-derived path/family", criteria)
        self.assertIn("Bianchi K and optical Q_cross", criteria)

    def test_forbids_lensing_fit_and_scalar_absorption(self) -> None:
        criteria = " ".join(row["accept"] for row in build_payload()["criteria"])

        self.assertIn("cannot be fit to residuals", criteria)
        self.assertIn("Q_det and Q_cross cannot absorb", criteria)
        self.assertIn("pressure, or anisotropic-stress", criteria)

    def test_source_derived_false_until_janus_path_rule(self) -> None:
        payload = build_payload()
        blockers = " ".join(payload["blockers"])

        self.assertFalse(payload["source_derived"])
        self.assertIn("Janus has not yet provided", blockers)
        self.assertIn("source-derived path/family rule", blockers)

    def test_markdown_renders_guardrails(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("segmentation invariance", markdown)
        self.assertIn("no lensing-fit amplitude", markdown)
        self.assertIn("Q_det/Q_cross absorption", markdown)


if __name__ == "__main__":
    unittest.main()
