from __future__ import annotations

import unittest

from scripts.build_p0_janus_source_tetrad_requirements import build_payload, render_markdown


class P0JanusSourceTetradRequirementsTests(unittest.TestCase):
    def test_payload_is_open_bounded_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-derived-tetrad-requirements-open")
        self.assertIn("no new source law", payload["scope"])
        self.assertTrue(payload["weak_field_tetrad_only_provisional"])
        self.assertTrue(payload["full_janus_tetrad_source_derivation_open"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["scalar_absorption_allowed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_starts_from_coupled_metric_source_equations(self) -> None:
        equations = " ".join(
            row["item"] + " " + row["working_form"] + " " + row["requirement"]
            for row in build_payload()["starting_equations"]
        )

        self.assertIn("G_plus[g_plus]", equations)
        self.assertIn("G_minus[g_minus]", equations)
        self.assertIn("cross_source_minus_to_plus", equations)
        self.assertIn("cross_source_plus_to_minus", equations)
        self.assertIn("Bianchi-compatible", equations)

    def test_required_tetrad_objects_are_source_derived(self) -> None:
        payload = build_payload()
        rows = {row["object"]: row for row in payload["requirements"]}

        self.assertIn("g_plus / g_minus", rows)
        self.assertIn("e_plus / e_minus", rows)
        self.assertIn("omega_plus / omega_minus", rows)
        self.assertIn("F_relative", rows)
        self.assertIn("L", rows)
        self.assertTrue(all(row["status"] == "open" for row in rows.values()))
        self.assertIn("g_{plus/minus mu nu} = eta_AB", rows["e_plus / e_minus"]["symbol"])
        self.assertIn("omega_plus - L omega_minus", rows["F_relative"]["symbol"])
        self.assertIn("Bianchi residuals", rows["L"]["must_be_source_derived"])

    def test_weak_field_branch_is_only_provisional(self) -> None:
        branch = build_payload()["weak_field_branch"]

        self.assertEqual(branch["name"], "Newtonian-gauge weak-field tetrad")
        self.assertIn("linear order", branch["form"])
        self.assertIn("provisional branch", branch["role"])
        self.assertFalse(branch["full_janus_derivation"])

    def test_forbids_fit_and_scalar_absorption(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("no observational fit", forbidden)
        self.assertIn("no scalar absorption", forbidden)
        self.assertIn("Q_cross/Q_det", forbidden)
        self.assertIn("do not promote the weak-field tetrad branch", forbidden)

    def test_markdown_renders_gates_and_requirements(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("# P0 Janus Source-Derived Tetrad Requirements", markdown)
        self.assertIn("Physics closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("| object | symbol | must be source-derived | not allowed | status |", markdown)
        self.assertIn("g_plus/g_minus, e_plus/e_minus, omega_plus/omega_minus", markdown)


if __name__ == "__main__":
    unittest.main()
