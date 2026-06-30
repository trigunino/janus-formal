from __future__ import annotations

import unittest

from scripts.build_p0_janus_metric_tetrad_source_branch_gate import build_payload, render_markdown


class P0JanusMetricTetradSourceBranchGateTests(unittest.TestCase):
    def test_branch_steps_link_metric_tetrad_connection_and_vlasov(self) -> None:
        text = " ".join(build_payload()["branch_steps"])

        self.assertIn("metric branch", text)
        self.assertIn("tetrads", text)
        self.assertIn("spin connections", text)
        self.assertIn("Christoffel", text)
        self.assertIn("Vlasov force", text)

    def test_acceptance_forbids_observational_selection(self) -> None:
        payload = build_payload()
        acceptance = " ".join(payload["acceptance"])

        self.assertIn("published/source-traced Janus", acceptance)
        self.assertIn("g_AB=eta_ab", acceptance)
        self.assertIn("no observational normalization", acceptance)
        self.assertTrue(payload["weakfield_metric_force_probe_available"])
        self.assertFalse(payload["source_selected_metric_branch_closed"])

    def test_no_prediction_claim(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Source-selected metric branch closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
