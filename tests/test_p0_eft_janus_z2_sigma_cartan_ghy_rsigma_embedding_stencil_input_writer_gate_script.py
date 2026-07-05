import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_embedding_stencil_input_writer_gate import (
    build_payload,
)


def _zero_christoffels():
    return [[[0.0, 0.0], [0.0, 0.0]], [[0.0, 0.0], [0.0, 0.0]]]


def _input() -> dict:
    offsets = [-0.1, 0.0, 0.1]
    bases = [2.0, 3.0]
    metric = []
    tangents = []
    second = []
    christoffels = []
    normals = []
    for base in bases:
        metric_row = []
        tangent_row = []
        second_row = []
        christoffel_row = []
        normal_row = []
        for offset in offsets:
            radius = base + offset
            metric_row.append([[1.0, 0.0], [0.0, radius * radius]])
            tangent_row.append([[0.0, 1.0]])
            second_row.append([[[0.0, 0.0]]])
            christoffel_row.append(_zero_christoffels())
            normal_row.append([1.0, 0.0])
        metric.append(metric_row)
        tangents.append(tangent_row)
        second.append(second_row)
        christoffels.append(christoffel_row)
        normals.append(normal_row)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.5, 1.0],
        "radial_offsets": offsets,
        "metric_covariant_stencil": metric,
        "tangent_vectors_stencil": tangents,
        "second_embedding_stencil": second,
        "christoffels_stencil": christoffels,
        "normal_covector_stencil": normals,
        "z2_orientation_sign": 1.0,
        "kappa_Z2Sigma": 2.0,
        "E_CartanGHY_provenance": "active Cartan-GHY embedding radial stencil",
    }


class CartanGHYRSigmaEmbeddingStencilInputWriterGateTests(unittest.TestCase):
    def test_embedding_stencil_writes_tensor_primitives(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "stencil.json"
            output_path = root / "tensor_primitives.json"
            input_path.write_text(json.dumps(_input()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertAlmostEqual(written["induced_metric_h_ab"][0][0][0], 4.0)
        self.assertAlmostEqual(written["induced_metric_h_ab"][1][0][0], 9.0)
        self.assertAlmostEqual(written["partial_R_induced_metric_h_ab"][0][0][0], 4.0)
        self.assertAlmostEqual(written["partial_R_induced_metric_h_ab"][1][0][0], 6.0)
        self.assertEqual(written["extrinsic_curvature_K_ab"], [[[0.0]], [[0.0]]])

    def test_missing_zero_offset_or_forbidden_flag_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "stencil.json"
            bad = _input()
            bad["radial_offsets"] = [-0.2, -0.1, 0.1]
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("include 0.0", payload["validation_error"])

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "stencil.json"
            bad = _input()
            bad["observational_curvature_fit_used"] = True
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("observational_curvature_fit_used", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
