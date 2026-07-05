import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_gaussian_collar_input_writer_gate import (
    build_payload,
)


def _input() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.5, 1.0],
        "radial_offsets": [-0.1, 0.0, 0.1],
        "ambient_coordinate_offsets": [
            [0.0, 0.0],
            [-0.1, 0.0],
            [0.1, 0.0],
            [0.0, -0.1],
            [0.0, 0.1],
            [0.1, 0.1],
        ],
        "intrinsic_coordinate_offsets": [[-0.1], [0.0], [0.1]],
        "induced_metric_h_ab": [[[4.0]], [[9.0]]],
        "partial_R_induced_metric_h_ab": [[[4.0]], [[6.0]]],
        "partial_R2_induced_metric_h_ab": [[[2.0]], [[2.0]]],
        "z2_orientation_sign": 1.0,
        "kappa_Z2Sigma": 2.0,
        "E_CartanGHY_provenance": "active Cartan-GHY Gaussian collar",
    }


class CartanGHYRSigmaGaussianCollarInputWriterGateTests(unittest.TestCase):
    def test_gaussian_collar_writes_local_chart_samples(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "collar.json"
            output_path = root / "local_chart.json"
            input_path.write_text(json.dumps(_input()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(written["local_chart_route"], "gaussian_collar_taylor_h_dh_d2h")
        self.assertAlmostEqual(written["metric_covariant_samples"][0][1][0][1][1], 4.0)
        self.assertAlmostEqual(written["metric_covariant_samples"][0][2][0][1][1], 4.41)
        self.assertAlmostEqual(written["embedding_coordinate_samples"][0][2][1][0], 0.1)

    def test_bad_metric_or_forbidden_flag_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "collar.json"
            bad = _input()
            bad["induced_metric_h_ab"][0] = [[0.0]]
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("nondegenerate", payload["validation_error"])

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "collar.json"
            bad = _input()
            bad["observational_H0_fit_used"] = True
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("observational_H0_fit_used", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
