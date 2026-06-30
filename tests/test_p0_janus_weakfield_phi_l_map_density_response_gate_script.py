from __future__ import annotations

import unittest

from scripts.build_p0_janus_weakfield_phi_l_map_density_response_gate import (
    build_payload,
    render_markdown,
)


class P0JanusWeakfieldPhiLMapDensityResponseGateTests(unittest.TestCase):
    def test_map_response_algebra_closes_but_dynamic_selection_remains_open(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "phi-l-map-density-response-algebra-closed-dynamic-selection-open",
        )
        self.assertTrue(payload["scalar_pullback_map_response_closed"])
        self.assertTrue(payload["volume_density_map_response_closed"])
        self.assertTrue(payload["delta_phi_map_response_slot_closed"])
        self.assertTrue(payload["l_density_separation_closed"])
        self.assertFalse(payload["jacobian_volume_identities_closed"])
        self.assertTrue(payload["same_l_stack_algebra_closed"])
        self.assertFalse(payload["same_l_source_selected"])
        self.assertEqual(payload["xi_map_equation_artifact"], "p0_janus_phi_l_xi_map_equation_gate")
        self.assertTrue(payload["xi_definition_closed"])
        self.assertFalse(payload["xi_solved_from_janus"])
        self.assertTrue(payload["mirror_variation_algebra_closed"])
        self.assertFalse(payload["dynamic_phi_l_selection_closed"])
        self.assertFalse(payload["mirror_map_response_closed"])
        self.assertFalse(payload["full_density_transport_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_response_rows_include_scalar_volume_slot_and_l_separation(self) -> None:
        rows = {row["name"]: row for row in build_payload()["response_rows"]}

        self.assertIn("delta_phi(phi^*rho_s)", rows["scalar_pullback_map_response"]["formula"])
        self.assertIn("xi^a nabla_a rho_s", rows["scalar_pullback_map_response"]["formula"])
        self.assertIn("rho_s nabla_a xi^a", rows["volume_density_map_response"]["formula"])
        self.assertIn("proper_density_input", rows["weakfield_delta_s00_slot"]["formula"])
        self.assertIn("delta_L affects velocity/stress projection", rows["l_dependence_separation"]["formula"])

    def test_open_requirements_target_phi_l_selection_mirror_and_non_dust(self) -> None:
        requirements = " ".join(build_payload()["open_requirements"])

        self.assertIn("xi=delta_phi", requirements)
        self.assertIn("J_phi/B_4vol", requirements)
        self.assertIn("same L", requirements)
        self.assertIn("phi^{-1}", requirements)
        self.assertIn("pressure/Pi", requirements)

    def test_no_fit_or_qdet_absorption(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["qdet_absorption_allowed"])
        self.assertFalse(payload["physics_closed"])

    def test_markdown_reports_open_physics(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Phi/L Map Density Response", markdown)
        self.assertIn("Xi definition closed: True", markdown)
        self.assertIn("Xi solved from Janus: False", markdown)
        self.assertIn("Delta phi map response slot closed: True", markdown)
        self.assertIn("Dynamic phi/L selection closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
