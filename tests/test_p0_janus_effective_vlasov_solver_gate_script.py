from __future__ import annotations

import unittest

from scripts.build_p0_janus_effective_vlasov_solver_gate import build_payload, render_markdown


class P0JanusEffectiveVlasovSolverGateTests(unittest.TestCase):
    def test_solver_layers_cover_force_moments_and_same_l(self) -> None:
        text = " ".join(build_payload()["solver_layers"])

        self.assertIn("phase-space advection", text)
        self.assertIn("A_Janus", text)
        self.assertIn("Q_ijk", text)
        self.assertIn("same-L", text)

    def test_required_inputs_keep_solver_non_predictive(self) -> None:
        payload = build_payload()
        inputs = " ".join(payload["required_inputs"])

        self.assertIn("metric/tetrad source branch", inputs)
        self.assertIn("B_4vol/dP", inputs)
        self.assertIn("initial distribution", inputs)
        self.assertTrue(payload["diagnostic_solver_probe_available"])
        self.assertTrue(payload["two_sector_vlasov_poisson_probe_available"])
        self.assertTrue(payload["metric_force_vlasov_step_probe_available"])
        self.assertTrue(payload["two_sector_metric_force_vlasov_probe_available"])
        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["effective_vlasov_solver_physics_ready"])

    def test_allowed_outputs_forbid_prediction(self) -> None:
        outputs = " ".join(build_payload()["allowed_outputs_now"])

        self.assertIn("diagnostic solver interface", outputs)
        self.assertIn("no prediction", outputs)
        self.assertIn("no survey comparison", outputs)

    def test_no_fit_or_prediction(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Effective Vlasov solver physics ready: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
