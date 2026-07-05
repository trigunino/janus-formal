import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_radial_primitives_input_writer_gate import (
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
        "induced_metric_h_ab": [
            [[4.0, 0.0], [0.0, 9.0]],
            [[1.0, 0.0], [0.0, 16.0]],
        ],
        "partial_R_induced_metric_h_ab": [
            [[2.0, 0.0], [0.0, 3.0]],
            [[0.5, 0.0], [0.0, 2.0]],
        ],
        "extrinsic_curvature_K_ab": [
            [[8.0, 0.0], [0.0, 18.0]],
            [[2.0, 0.0], [0.0, 32.0]],
        ],
        "partial_R_extrinsic_curvature_K_ab": [
            [[1.0, 0.0], [0.0, 2.0]],
            [[3.0, 0.0], [0.0, 4.0]],
        ],
        "z2_orientation_sign": 1.0,
        "kappa_Z2Sigma": 2.0,
        "E_CartanGHY_provenance": "active Cartan-GHY tensor radial variation",
    }


class CartanGHYRSigmaRadialPrimitivesInputWriterGateTests(unittest.TestCase):
    def test_active_tensors_write_radial_variation_primitives(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "tensor_input.json"
            output_path = root / "variation_input.json"
            input_path.write_text(json.dumps(_input()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertAlmostEqual(written["sqrt_abs_h"][0], 6.0)
        self.assertAlmostEqual(written["sqrt_abs_h"][1], 4.0)
        self.assertEqual(written["K_trace"], [4.0, 4.0])
        self.assertAlmostEqual(written["trace_h_inv_partial_R_h"][0], 5.0 / 6.0)
        self.assertAlmostEqual(written["trace_h_inv_partial_R_h"][1], 0.625)
        self.assertAlmostEqual(written["partial_R_K_trace"][0], -43.0 / 36.0)
        self.assertAlmostEqual(written["partial_R_K_trace"][1], 2.0)

    def test_forbidden_flag_or_bad_geometry_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "tensor_input.json"
            bad = _input()
            bad["archived_z4_background_reuse_used"] = True
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("archived_z4_background_reuse_used", payload["validation_error"])

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "tensor_input.json"
            bad = _input()
            bad["induced_metric_h_ab"][0] = [[1.0, 0.0], [0.0, 0.0]]
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("nondegenerate", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
