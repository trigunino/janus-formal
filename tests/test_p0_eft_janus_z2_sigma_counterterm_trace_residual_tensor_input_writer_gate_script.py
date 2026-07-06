import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_counterterm_trace_residual_tensor_input_writer_gate import (
    build_payload,
)


def _active(**fields):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
    }
    payload.update(fields)
    return payload


class CountertermTraceResidualTensorInputWriterGateTests(unittest.TestCase):
    def test_writes_isotropic_tensors_from_traces(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q_path = root / "q.json"
            trace_path = root / "trace.json"
            metric_path = root / "metric.json"
            extrinsic_path = root / "extrinsic.json"
            q_path.write_text(
                json.dumps(
                    _active(unit_intrinsic_metric_q_ab=[[1.0, 0.0], [0.0, 2.0]])
                ),
                encoding="utf-8",
            )
            trace_path.write_text(
                json.dumps(
                    _active(
                        a_grid=[0.5, 1.0],
                        R_h_trace_values=[6.0, 12.0],
                        R_K_trace_values=[8.0, 16.0],
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                q_path=q_path,
                trace_path=trace_path,
                metric_output_path=metric_path,
                extrinsic_output_path=extrinsic_path,
            )
            metric = json.loads(metric_path.read_text(encoding="utf-8"))
            extrinsic = json.loads(extrinsic_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(metric["R_h_ab"][0], [[3.0, 0.0], [0.0, 1.5]])
        self.assertEqual(extrinsic["R_K_ab"][1], [[8.0, 0.0], [0.0, 4.0]])

    def test_missing_trace_input_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                q_path=Path(tmp) / "missing_q.json",
                trace_path=Path(tmp) / "missing_trace.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("counterterm_trace_residual_inputs", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
