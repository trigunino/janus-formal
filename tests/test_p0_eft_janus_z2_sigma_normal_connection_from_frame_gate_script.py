import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_normal_connection_from_frame_gate import (
    build_payload,
)


def _manifest() -> dict:
    u_grid = [0.0, 1.0]
    basis = []
    derivative = []
    for u in u_grid:
        theta = u
        c = math.cos(theta)
        s = math.sin(theta)
        basis.append([[c, s], [-s, c]])
        derivative.append([[-s, c], [-c, -s]])
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_normal_frame_connection_primitives",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "lambda_grid": [1.0],
        "collar_coordinate_u_grid": u_grid,
        "normal_frame_basis_lambda_u": [basis],
        "partial_u_normal_frame_basis_lambda_u": [derivative],
        "connection_u_matrix_lambda_u": [[[[0.0, 0.0], [0.0, 0.0]] for _ in u_grid]],
        "ambient_metric_lambda_u": [[[[1.0, 0.0], [0.0, 1.0]] for _ in u_grid]],
        "primitive_provenance": {
            "normal_frame_basis_lambda_u": "active_collar_normal_frame",
            "partial_u_normal_frame_basis_lambda_u": "active_collar_frame_derivative",
            "connection_u_matrix_lambda_u": "active_collar_levi_civita_connection",
            "ambient_metric_lambda_u": "active_collar_metric",
        },
    }


class NormalConnectionFromFrameGateScriptTest(unittest.TestCase):
    def test_blocks_without_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(Path(tmp) / "missing.json", Path(tmp) / "out.json")
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["blocker"], "normal_connection_frame_primitives_missing")

    def test_writes_omega_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "manifest.json"
            output_path = Path(tmp) / "omega.json"
            input_path.write_text(json.dumps(_manifest()), encoding="utf-8")
            payload = build_payload(input_path, output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["normal_connection_ready"])
        self.assertAlmostEqual(written["normal_connection_omega_perp_lambda_u"][0][0][0][1], -1.0)


if __name__ == "__main__":
    unittest.main()
