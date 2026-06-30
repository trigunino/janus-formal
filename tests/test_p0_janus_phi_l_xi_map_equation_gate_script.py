from __future__ import annotations

import unittest

from scripts.build_p0_janus_phi_l_xi_map_equation_gate import (
    build_payload,
    render_markdown,
)


class P0JanusPhiLXiMapEquationGateTests(unittest.TestCase):
    def test_xi_algebra_closes_not_dynamic_selection(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "xi-map-variation-algebra-closed-source-equation-open")
        self.assertTrue(payload["xi_definition_closed"])
        self.assertTrue(payload["pullback_variation_closed"])
        self.assertTrue(payload["inverse_map_variation_closed"])
        self.assertTrue(payload["l_inverse_variation_closed"])
        self.assertTrue(payload["formal_map_el_written"])
        self.assertEqual(
            payload["ephi_el_origin_artifact"],
            "p0_janus_phi_l_ephi_el_variational_origin_gate",
        )
        self.assertTrue(payload["e_phi_candidate_written"])
        self.assertTrue(payload["e_l_candidate_written"])
        self.assertTrue(payload["source_coupled_action_required"])
        self.assertFalse(payload["published_janus_e_phi_supplied"])
        self.assertFalse(payload["published_janus_e_l_supplied"])
        self.assertFalse(payload["janus_e_phi_supplied"])
        self.assertFalse(payload["janus_e_l_supplied"])
        self.assertFalse(payload["xi_solved_from_janus"])
        self.assertFalse(payload["dynamic_phi_l_selection_closed"])
        self.assertTrue(payload["mirror_variation_algebra_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_variation_rows_include_xi_pullback_inverse_and_l_generator(self) -> None:
        rows = {row["name"]: row for row in build_payload()["variation_rows"]}

        self.assertIn("delta_phi^a o phi^{-1}", rows["xi_definition"]["formula"])
        self.assertIn("delta_phi(phi^*A)=phi^*(Lie_xi A)", rows["pullback_variation"]["formula"])
        self.assertIn("- (phi^{-1})_* xi", rows["inverse_map_variation"]["formula"])
        self.assertIn("Lambda = delta L L^{-1}", rows["l_generator"]["formula"])
        self.assertIn("E_phi_a xi^a", rows["formal_map_el"]["formula"])

    def test_open_requirements_block_fake_solution(self) -> None:
        requirements = " ".join(build_payload()["open_requirements"])

        self.assertIn("E_phi_a", requirements)
        self.assertIn("E_L_AB", requirements)
        self.assertIn("boundary/gauge", requirements)
        self.assertIn("K, Q_cross and Vlasov", requirements)
        self.assertIn("reject observational residual tuning", requirements)

    def test_markdown_reports_source_open(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Xi Map Equation", markdown)
        self.assertIn("Xi definition closed: True", markdown)
        self.assertIn("E_phi candidate written: True", markdown)
        self.assertIn("Janus E_phi supplied: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
