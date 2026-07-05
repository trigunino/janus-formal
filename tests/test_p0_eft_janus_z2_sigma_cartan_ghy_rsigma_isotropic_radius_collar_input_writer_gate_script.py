import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_isotropic_radius_collar_input_writer_gate import (
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
        "R_Sigma_of_a": [2.0, 3.0],
        "unit_intrinsic_metric_q_ab": [[1.0]],
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
        "z2_orientation_sign": 1.0,
        "kappa_Z2Sigma": 2.0,
        "E_CartanGHY_provenance": "active Cartan-GHY isotropic radius collar",
    }


class CartanGHYRSigmaIsotropicRadiusCollarInputWriterGateTests(unittest.TestCase):
    def test_isotropic_radius_writes_gaussian_collar_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "radius.json"
            output_path = root / "collar.json"
            input_path.write_text(json.dumps(_input()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(written["gaussian_collar_route"], "isotropic_radius_RSigma_squared_unit_metric")
        self.assertEqual(written["induced_metric_h_ab"], [[[4.0]], [[9.0]]])
        self.assertEqual(written["partial_R_induced_metric_h_ab"], [[[4.0]], [[6.0]]])
        self.assertEqual(written["partial_R2_induced_metric_h_ab"], [[[2.0]], [[2.0]]])

    def test_bad_radius_or_forbidden_flag_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "radius.json"
            bad = _input()
            bad["R_Sigma_of_a"][0] = 0.0
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("R_Sigma_of_a", payload["validation_error"])

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "radius.json"
            bad = _input()
            bad["archived_z4_background_reuse_used"] = True
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("archived_z4_background_reuse_used", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
