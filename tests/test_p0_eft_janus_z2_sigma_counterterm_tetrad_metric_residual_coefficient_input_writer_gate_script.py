import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_metric_residual_coefficient_input_writer_gate import (
    build_payload,
)


def _active_payload(field: str, value):
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "fitted_counterterm_coefficient_used": False,
        field: value,
        "provenance": f"active_{field}",
    }


class CountertermTetradMetricResidualCoefficientInputWriterGateTests(unittest.TestCase):
    def test_missing_inputs_keep_gate_blocked(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                metric_residual_input_path=root / "missing_metric.json",
                coframe_trace_input_path=root / "missing_coframe.json",
                output_path=root / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["tetrad_metric_residual_coefficient_value_ready"])
        self.assertIn(
            "active_metric_residual_tensor_R_h_ab",
            payload["nearest_frontier"]["blocks"],
        )

    def test_active_metric_and_coframe_inputs_write_coefficient(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            metric = root / "metric.json"
            coframe = root / "coframe.json"
            output = root / "out.json"
            metric.write_text(json.dumps(_active_payload("R_h_ab", [[1.0, 0.5], [0.5, 2.0]])), encoding="utf-8")
            coframe.write_text(json.dumps(_active_payload("e_bI_on_Sigma", [[1.0, 0.0], [0.0, 1.0]])), encoding="utf-8")

            payload = build_payload(
                metric_residual_input_path=metric,
                coframe_trace_input_path=coframe,
                output_path=output,
            )
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["coefficient_output_written"])
        self.assertEqual(written["R_e_metric_aI"], [[2.0, 1.0], [1.0, 4.0]])
        self.assertFalse(written["fitted_counterterm_coefficient_used"])

    def test_invalid_active_inputs_do_not_write_coefficient(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            metric = root / "metric.json"
            coframe = root / "coframe.json"
            output = root / "out.json"
            metric_payload = _active_payload("R_h_ab", [[1.0, float("nan")], [0.5, 2.0]])
            coframe_payload = _active_payload("e_bI_on_Sigma", [[1.0, 0.0], [0.0, 1.0]])
            coframe_payload["provenance"] = ""
            metric.write_text(json.dumps(metric_payload), encoding="utf-8")
            coframe.write_text(json.dumps(coframe_payload), encoding="utf-8")

            payload = build_payload(
                metric_residual_input_path=metric,
                coframe_trace_input_path=coframe,
                output_path=output,
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(output.exists())
        self.assertIn("provenance", payload["coframe_trace_validation_error"])


if __name__ == "__main__":
    unittest.main()
