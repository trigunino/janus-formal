import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_sigma_counterterm_residual_tensors_from_local_density_action import (
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


class CountertermResidualTensorsFromLocalDensityActionTests(unittest.TestCase):
    def test_writes_metric_and_extrinsic_residual_tensors(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q_path = root / "q.json"
            density_path = root / "density.json"
            metric_path = root / "metric.json"
            extrinsic_path = root / "extrinsic.json"
            q_path.write_text(
                json.dumps(_active(unit_intrinsic_metric_q_ab=[[1.0, 0.0], [0.0, 1.0]])),
                encoding="utf-8",
            )
            density_path.write_text(
                json.dumps(
                    _active(
                        local_density_action_derived=True,
                        density_expression_status="explicit",
                        L_ct_expression="alpha*R_Sigma + beta*K_trace",
                        parameters={"alpha": 2.0, "beta": 3.0},
                        a_grid=[0.5, 1.0],
                        R_Sigma_of_a=[2.0, 3.0],
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                q_path=q_path,
                density_path=density_path,
                metric_output_path=metric_path,
                extrinsic_output_path=extrinsic_path,
            )
            metric = json.loads(metric_path.read_text(encoding="utf-8"))
            extrinsic = json.loads(extrinsic_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertAlmostEqual(metric["R_h_q_contract_values"][0], 0.25)
        self.assertAlmostEqual(extrinsic["R_K_q_contract_values"][0], -1.5)
        self.assertEqual(metric["R_Sigma_values"], [2.0, 3.0])
        self.assertEqual(extrinsic["R_Sigma_values"], [2.0, 3.0])

    def test_blocks_without_density_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                q_path=root / "missing_q.json",
                density_path=root / "missing_density.json",
                metric_output_path=root / "metric.json",
                extrinsic_output_path=root / "extrinsic.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("counterterm_local_density_action_inputs", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
