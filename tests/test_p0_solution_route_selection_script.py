from __future__ import annotations

import unittest

from scripts.build_p0_solution_route_selection import build_payload, render_markdown


class P0SolutionRouteSelectionTests(unittest.TestCase):
    def test_route_selection_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "route-selection-open")
        self.assertIsNone(payload["selected_route"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_routes_cover_minimal_geometry_action_and_matter(self) -> None:
        routes = {row["route"] for row in build_payload()["routes"]}

        self.assertIn("minimal_lorentz_dust", routes)
        self.assertIn("cartan_integrability", routes)
        self.assertIn("variational_noether", routes)
        self.assertIn("kinetic_moment_extension", routes)

    def test_promotion_tests_block_shortcuts(self) -> None:
        tests = " ".join(build_payload()["promotion_tests"])

        self.assertIn("R_plus and R_minus", tests)
        self.assertIn("Q_det and Q_cross remain separate", tests)
        self.assertIn("accepted Janus sources", tests)

    def test_markdown_names_parallel_work(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("minimal_lorentz_dust", markdown)
        self.assertIn("cartan_integrability", markdown)
        self.assertIn("variational_noether", markdown)


if __name__ == "__main__":
    unittest.main()
