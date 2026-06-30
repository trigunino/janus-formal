from __future__ import annotations

import unittest

from scripts.build_p0_same_l_bridge_induces_m_k_qcross_gate import (
    build_payload,
    render_markdown,
)


class P0SameLBridgeInducesMKQcrossGateTests(unittest.TestCase):
    def test_same_l_stack_algebra_closes_without_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "same-l-bridge-stack-algebra-closed-source-open")
        self.assertTrue(payload["same_l_induces_m"])
        self.assertTrue(payload["same_l_induces_k"])
        self.assertTrue(payload["same_l_induces_qcross"])
        self.assertTrue(payload["same_l_induces_vlasov_moments"])
        self.assertTrue(payload["same_l_stack_algebra_closed"])
        self.assertFalse(payload["l_source_selected"])
        self.assertFalse(payload["lorentz_admissibility_proved"])
        self.assertFalse(payload["bianchi_residuals_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_definitions_link_l_to_m_k_qcross_and_vlasov(self) -> None:
        rows = {row["name"]: row for row in build_payload()["bridge_definitions"]}

        self.assertIn("L_{o->s}", rows["single_tetrad_bridge"]["formula"])
        self.assertIn("M_{o->s}^{mu}{}_{alpha}", rows["coordinate_bridge"]["formula"])
        self.assertIn("L_{o->s}^{A}{}_{B}", rows["coordinate_bridge"]["formula"])
        self.assertIn("K_s^{mu nu}=T_{o->s}^{mu nu}", rows["stress_transport"]["formula"])
        self.assertIn("Q_cross", rows["optical_qcross"]["formula"])
        self.assertIn("p_{o->s}^{A}=L", rows["vlasov_moment_transport"]["formula"])
        self.assertIn("L_{s->o}=L_{o->s}^{-1}", rows["mirror_branch"]["formula"])

    def test_scalar_absorption_is_forbidden(self) -> None:
        payload = build_payload()
        results = {row["claim"]: row for row in payload["algebraic_results"]}

        self.assertFalse(payload["scalar_absorption_allowed"])
        self.assertFalse(payload["qcross_is_measure"])
        self.assertFalse(payload["b4vol_is_stf_source"])
        self.assertTrue(results["no_scalar_absorption"]["closed"])
        self.assertIn("B4vol/Q_det", results["no_scalar_absorption"]["result"])
        self.assertIn("Q_cross is optical", results["no_scalar_absorption"]["result"])

    def test_open_requirements_keep_janus_source_obligations(self) -> None:
        text = " ".join(build_payload()["open_requirements"])

        self.assertIn("source-select L", text)
        self.assertIn("L^T eta L=eta", text)
        self.assertIn("mirror inverse", text)
        self.assertIn("D L", text)
        self.assertIn("R_plus=0 and R_minus=0", text)

    def test_markdown_reports_algebra_closed_source_open(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Same-L Bridge Induces M/K/Q_cross", markdown)
        self.assertIn("Same-L stack algebra closed: True", markdown)
        self.assertIn("L source selected: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
