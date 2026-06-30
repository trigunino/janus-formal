from __future__ import annotations

import unittest

from scripts.build_p0_route_c_spath_metric_stress_variation_gate import (
    build_payload,
    render_markdown,
)


class P0RouteCSPathMetricStressVariationGateTests(unittest.TestCase):
    def test_gate_writes_contract_but_blocks_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "spath-metric-stress-variation-gate-open")
        self.assertTrue(payload["scalar_density_contract_written"])
        self.assertFalse(payload["scalar_density_complete"])
        self.assertTrue(payload["hilbert_stress_definition_written"])
        self.assertTrue(payload["volume_variation_identity_closed"])
        self.assertTrue(payload["metric_variation_chain_written"])
        self.assertFalse(payload["metric_variation_chain_complete"])
        self.assertFalse(payload["k_plus_metric_variation_derived"])
        self.assertFalse(payload["k_minus_metric_variation_derived"])
        self.assertFalse(payload["pressure_pi_tensor_terms_derived"])
        self.assertFalse(payload["scalar_absorption_allowed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_metric_variation_obligations(self) -> None:
        rows = {row["object"]: row for row in build_payload()["variation_rows"]}

        self.assertEqual(
            set(rows),
            {
                "Hilbert_stress_definition",
                "volume_density",
                "path_cost_metric_chain",
                "lorentz_transport_metric_chain",
                "boundary_metric_chain",
                "pressure_pi_tensor_extraction",
            },
        )
        self.assertTrue(rows["volume_density"]["closed"])
        self.assertFalse(rows["path_cost_metric_chain"]["closed"])
        self.assertIn("K_s", rows["Hilbert_stress_definition"]["formula"])
        self.assertIn("Pi_s", rows["pressure_pi_tensor_extraction"]["formula"])

    def test_markdown_reports_open_tensor_variation(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Metric-Stress Variation Gate", markdown)
        self.assertIn("Scalar density complete: False", markdown)
        self.assertIn("K_plus metric variation derived: False", markdown)
        self.assertIn("Scalar absorption allowed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
