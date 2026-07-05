import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_sector_metric_time_direction_from_unit_throat_chart_gate import (
    build_payload,
)


def _active(**extra):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
    }
    payload.update(extra)
    return payload


class P0EFTJanusZ2SigmaSectorMetricTimeDirectionFromUnitThroatChartGateTests(unittest.TestCase):
    def test_gate_writes_metric_and_time_direction(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q_path = root / "q.json"
            grid_path = root / "grid.json"
            metric_path = root / "metric.json"
            time_path = root / "time.json"
            q_path.write_text(
                json.dumps(_active(unit_intrinsic_metric_q_ab=[[1.0, 0.0], [0.0, 1.0]])),
                encoding="utf-8",
            )
            grid_path.write_text(json.dumps(_active(a_grid=[0.5, 1.0])), encoding="utf-8")

            payload = build_payload(
                q_path=q_path,
                grid_path=grid_path,
                metric_output_path=metric_path,
                time_output_path=time_path,
            )

            metric = json.loads(metric_path.read_text(encoding="utf-8"))
            time = json.loads(time_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(metric["metric_plus_munu_values"][0][0][0], -1.0)
        self.assertEqual(metric["metric_plus_munu_values"][0][1][1], 1.0)
        self.assertEqual(metric["metric_plus_munu_values"][0][3][3], 1.0)
        self.assertEqual(time["time_direction_plus_values"][0], [1.0, 0.0, 0.0, 0.0])

    def test_missing_inputs_block_gate(self):
        payload = build_payload()

        self.assertIn("unit_intrinsic_metric_q_ab_inputs", payload["input_exists"])


if __name__ == "__main__":
    unittest.main()
