from __future__ import annotations

import unittest

from scripts.build_p0_janus_phi_l_ephi_el_variational_origin_gate import (
    build_payload,
    render_markdown,
)


class P0JanusPhiLEphiElVariationalOriginGateTests(unittest.TestCase):
    def test_candidate_equations_are_written_but_source_action_remains_open(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "candidate-ephi-el-derived-algebraically-source-action-open",
        )
        self.assertTrue(payload["xi_variation_variable_closed"])
        self.assertTrue(payload["lambda_variation_variable_closed"])
        self.assertTrue(payload["e_phi_candidate_written"])
        self.assertTrue(payload["e_l_candidate_written"])
        self.assertFalse(payload["pure_pullback_selects_phi_l"])
        self.assertFalse(payload["lorentz_l_selects_unique_bridge"])
        self.assertTrue(payload["source_coupled_action_required"])
        self.assertFalse(payload["published_janus_e_phi_supplied"])
        self.assertFalse(payload["published_janus_e_l_supplied"])
        self.assertFalse(payload["dynamic_phi_l_selection_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_candidate_equations_cover_density_stress_l_and_mirror(self) -> None:
        rows = {row["name"]: row for row in build_payload()["candidate_equations"]}

        self.assertIn("rho_to nabla_a xi^a", rows["E_phi_density"]["formula"])
        self.assertIn("Lie_xi T_to", rows["E_phi_stress"]["formula"])
        self.assertIn("antisym_AB", rows["E_L_lorentz"]["formula"])
        self.assertIn("GL/strain action", rows["E_L_strain"]["formula"])
        self.assertIn("Ad_{L^{-1}}", rows["mirror_equations"]["formula"])

    def test_no_fit_or_scalar_absorption_route(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["not_derive_from"])

        self.assertIn("observational fitting", forbidden)
        self.assertIn("Q_cross/Q_det absorption", forbidden)
        self.assertIn("independent L", forbidden)
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["qdet_qcross_scalar_absorption_allowed"])

    def test_markdown_reports_variational_origin(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("E_phi/E_L Variational Origin", markdown)
        self.assertIn("Source-coupled action required: True", markdown)
        self.assertIn("Published Janus E_phi supplied: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
