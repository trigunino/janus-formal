from __future__ import annotations

import unittest

from scripts.build_p0_janus_kinetic_moment_hierarchy_equations import build_payload, render_markdown


class P0JanusKineticMomentHierarchyEquationsTests(unittest.TestCase):
    def test_moment_equations_show_hierarchy(self) -> None:
        payload = build_payload()
        equations = " ".join(row["equation"] for row in payload["moment_equations"])

        self.assertIn("D_t rho", equations)
        self.assertIn("P_ij", equations)
        self.assertIn("Q_ijk", equations)
        self.assertTrue(payload["third_moment_required_for_general_closure"])

    def test_decomposition_keeps_pressure_and_pi_separate(self) -> None:
        decomposition = " ".join(build_payload()["decompositions"])

        self.assertIn("P_ij=p delta_ij+Pi_ij", decomposition)
        self.assertIn("Tr(Pi)=0", decomposition)

    def test_janus_links_do_not_close_hierarchy(self) -> None:
        payload = build_payload()
        links = " ".join(payload["janus_source_links"])

        self.assertIn("G0i shift operator", links)
        self.assertIn("not a closure", links)
        self.assertFalse(payload["hierarchy_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_no_fit_or_physics_claim(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])

    def test_markdown_reports_open_hierarchy(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Hierarchy closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
