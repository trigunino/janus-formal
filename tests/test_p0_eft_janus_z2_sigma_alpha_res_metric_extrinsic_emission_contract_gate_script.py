from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_sigma_alpha_res_metric_extrinsic_emission_contract_gate import (
    build_payload,
    render_markdown,
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


class AlphaResMetricExtrinsicEmissionContractGateTests(unittest.TestCase):
    def test_blocks_without_trace_values(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(trace_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["trace_values_ready"])
        self.assertEqual(
            payload["primary_blocker"],
            "counterterm_trace_residual_inputs_from_sigma_boundary_variation",
        )

    def test_contract_can_emit_when_trace_values_exist(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q_path = root / "q.json"
            trace_path = root / "trace.json"
            metric_path = root / "metric.json"
            extrinsic_path = root / "extrinsic.json"
            q_path.write_text(
                json.dumps(_active(unit_intrinsic_metric_q_ab=[[1.0, 0.0], [0.0, 1.0]])),
                encoding="utf-8",
            )
            trace_path.write_text(
                json.dumps(
                    _active(
                        a_grid=[0.5, 1.0],
                        R_h_trace_values=[2.0, 4.0],
                        R_K_trace_values=[6.0, 8.0],
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

            self.assertTrue(payload["trace_values_ready"])
            self.assertTrue(payload["gate_passed"])
            self.assertTrue(payload["R_h_ab_emitted"])
            self.assertTrue(payload["R_K_ab_emitted"])
            self.assertIn("R_h_trace_values", payload["contract"]["required_fields"])
            self.assertTrue(metric_path.exists())
            self.assertTrue(extrinsic_path.exists())

    def test_markdown_reports_blocker(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Alpha_res Metric/Extrinsic", markdown)
        self.assertIn("counterterm_trace_residual_inputs", markdown)


if __name__ == "__main__":
    unittest.main()
