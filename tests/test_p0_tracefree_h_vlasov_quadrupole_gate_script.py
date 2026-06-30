from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_vlasov_quadrupole_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHVlasovQuadrupoleGateTests(unittest.TestCase):
    def test_distribution_defines_moments_but_not_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-vlasov-quadrupole-candidate-open")
        self.assertEqual(payload["qtf_candidate"], "kinetic_quadrupole_vlasov")
        self.assertTrue(payload["distribution_defines_density_pressure_pi_tf"])
        self.assertTrue(payload["trace_free_quadrupole_defined"])
        self.assertFalse(payload["can_source_qtf"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_moments_include_density_pressure_and_pi_tf(self) -> None:
        moments = {row["moment"]: row for row in build_payload()["moment_definitions"]}

        self.assertIn("density", moments)
        self.assertIn("pressure", moments)
        self.assertIn("pi_tf_quadrupole", moments)
        self.assertIn("int f", moments["density"]["formula"])
        self.assertIn("Tr(P_ij)/3", moments["pressure"]["formula"])
        self.assertIn("P_ij-p delta_ij", moments["pi_tf_quadrupole"]["formula"])

    def test_quadrupole_requires_vlasov_hierarchy_not_algebraic_closure(self) -> None:
        payload = build_payload()
        couplings = {row["equation"]: row for row in payload["hierarchy_couplings"]}
        guardrails = " ".join(payload["guardrails"])

        self.assertFalse(payload["moment_hierarchy_closed"])
        self.assertFalse(payload["full_vlasov_transport_closed"])
        self.assertFalse(payload["quadrupole_evolution_algebraically_closed"])
        self.assertFalse(couplings["pressure_pi_transport"]["closed"])
        self.assertFalse(couplings["quadrupole_evolution"]["closed"])
        self.assertIn("higher moments", couplings["quadrupole_evolution"]["depends_on"])
        self.assertIn("do not close the quadrupole algebraically", guardrails)

    def test_qtf_source_requires_janus_action_and_same_l_measure(self) -> None:
        payload = build_payload()
        requirements = {row["requirement"]: row for row in payload["acceptance_requirements"]}

        self.assertFalse(payload["janus_kinetic_action_source_closed"])
        self.assertFalse(payload["same_l_phase_space_measure_closed"])
        self.assertIn("Janus kinetic action/source", requirements)
        self.assertIn("same-L phase-space measure", requirements)
        self.assertFalse(requirements["Janus kinetic action/source"]["closed"])
        self.assertFalse(requirements["same-L phase-space measure"]["closed"])

    def test_forbids_fit_routes_and_markdown_reports_gate(self) -> None:
        payload = build_payload()
        markdown = render_markdown(payload)

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_residual_fit"])
        self.assertIn("Vlasov Quadrupole Gate", markdown)
        self.assertIn("Can source Q_TF: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("same-L phase-space measure", markdown)


if __name__ == "__main__":
    unittest.main()
