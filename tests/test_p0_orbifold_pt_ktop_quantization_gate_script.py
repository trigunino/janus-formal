from __future__ import annotations

import unittest

from scripts.build_p0_orbifold_pt_ktop_quantization_gate import build_payload, render_markdown


class P0OrbifoldPTKTopQuantizationGateTests(unittest.TestCase):
    def test_quantization_gate_discretizes_but_does_not_fix(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "orbifold-pt-ktop-quantization-gate-open")
        self.assertTrue(payload["k_top_quantization_condition_written"])
        self.assertTrue(payload["large_gauge_can_discretize"])
        self.assertTrue(payload["pt_can_filter_sign_or_parity"])
        self.assertTrue(payload["anomaly_inflow_could_fix_if_anomaly_known"])
        self.assertFalse(payload["defect_anomaly_polynomial_known"])
        self.assertFalse(payload["gauge_group_normalization_fixed"])
        self.assertFalse(payload["defect_dimension_degree_fixed"])
        self.assertFalse(payload["janus_source_normalization_found"])
        self.assertFalse(payload["minimal_level_choice_allowed_without_axiom"])
        self.assertFalse(payload["k_top_unique_value_fixed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_possible_k_top_selection_mechanisms(self) -> None:
        rows = {row["mechanism"]: row for row in build_payload()["rows"]}

        self.assertEqual(
            set(rows),
            {
                "large_gauge_invariance",
                "pt_orientation_parity",
                "anomaly_inflow",
                "minimal_integer_level",
                "janus_source_normalization",
            },
        )
        self.assertFalse(rows["large_gauge_invariance"]["fixes_unique_value"])
        self.assertEqual(rows["anomaly_inflow"]["fixes_unique_value"], "conditional")
        self.assertEqual(rows["janus_source_normalization"]["fixes_unique_value"], "not-available")

    def test_markdown_reports_open_k_top(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("k_top Quantization Gate", markdown)
        self.assertIn("Large gauge can discretize: True", markdown)
        self.assertIn("k_top unique value fixed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
