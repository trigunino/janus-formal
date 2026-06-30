from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_map_constraint_counting import (
    build_payload,
    render_markdown,
)


class P0StueckelbergMapConstraintCountingTests(unittest.TestCase):
    def test_artifact_is_bounded_and_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["artifact"], "stueckelberg-map-constraint-counting")
        self.assertEqual(payload["status"], "bounded-counting-overconstraint-risk")
        self.assertFalse(payload["source_derived"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["fit_to_observations"])

    def test_unknown_count_is_phi_four_plus_l_six(self) -> None:
        unknowns = {row["field"]: row for row in build_payload()["unknowns"]}

        self.assertEqual(unknowns["phi"]["degree_of_freedom"], 4)
        self.assertEqual(unknowns["L"]["degree_of_freedom"], 6)
        self.assertEqual(build_payload()["total_unknown_dof"], 10)

    def test_required_constraint_classes_are_present(self) -> None:
        text = " ".join(
            row["name"] + " " + row["count"] + " " + row["risk"]
            for row in build_payload()["constraints"]
        )

        self.assertIn("receiver geodesic conditions", text)
        self.assertIn("E_phi", text)
        self.assertIn("E_L", text)
        self.assertIn("mirror inverse", text)
        self.assertIn("same L for K/Q_cross", text)
        self.assertIn("residual closures", text)
        self.assertIn("phi^{-1}", text)
        self.assertIn("L^{-1}", text)

    def test_overconstraint_risks_and_escape_routes_are_explicit(self) -> None:
        payload = build_payload()
        risks = " ".join(payload["overconstraint_risks"])
        routes = {row["route"]: row for row in payload["escape_routes"]}

        self.assertIn("exceed the 4 phi", risks)
        self.assertIn("exceed the 6 Lorentz", risks)
        self.assertIn("minus-sector equations are checks", risks)
        self.assertIn("symmetry", routes)
        self.assertIn("FLRW", routes)
        self.assertIn("dust congruence only", routes)
        self.assertIn("gauge freedom", routes)
        self.assertEqual(routes["gauge freedom"]["status"], "requires-rank-proof")

    def test_markdown_reports_counting_and_non_readiness(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Total unknown dof: 10", markdown)
        self.assertIn("| phi | 4 |", markdown)
        self.assertIn("| L | 6 |", markdown)
        self.assertIn("not prediction ready", markdown)


if __name__ == "__main__":
    unittest.main()
