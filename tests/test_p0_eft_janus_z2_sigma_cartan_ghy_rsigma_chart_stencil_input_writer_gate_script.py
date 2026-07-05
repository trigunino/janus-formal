import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_chart_stencil_input_writer_gate import (
    build_payload,
)


def _input() -> dict:
    offsets = [-0.1, 0.0, 0.1]
    bases = [2.0, 3.0]
    metric = []
    derivatives = []
    tangents = []
    second = []
    gradients = []
    for base in bases:
        metric_row = []
        derivative_row = []
        tangent_row = []
        second_row = []
        gradient_row = []
        for offset in offsets:
            radius = base + offset
            metric_row.append([[1.0, 0.0], [0.0, radius * radius]])
            dg = [[[0.0, 0.0], [0.0, 2.0 * radius]], [[0.0, 0.0], [0.0, 0.0]]]
            derivative_row.append(dg)
            tangent_row.append([[0.0, 1.0]])
            second_row.append([[[0.0, 0.0]]])
            gradient_row.append([1.0, 0.0])
        metric.append(metric_row)
        derivatives.append(derivative_row)
        tangents.append(tangent_row)
        second.append(second_row)
        gradients.append(gradient_row)
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
        "metric_derivatives_stencil": derivatives,
        "tangent_vectors_stencil": tangents,
        "second_embedding_stencil": second,
        "level_gradient_covector_stencil": gradients,
        "normal_norm_sign": 1.0,
        "orientation_sign": 1.0,
        "z2_orientation_sign": 1.0,
        "kappa_Z2Sigma": 2.0,
        "E_CartanGHY_provenance": "active Cartan-GHY chart radial stencil",
    }


class CartanGHYRSigmaChartStencilInputWriterGateTests(unittest.TestCase):
    def test_chart_stencil_writes_embedding_stencil_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "chart.json"
            output_path = root / "embedding_stencil.json"
            input_path.write_text(json.dumps(_input()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertAlmostEqual(written["normal_covector_stencil"][0][1][0], 1.0)
        self.assertAlmostEqual(written["christoffels_stencil"][0][1][0][1][1], -2.0)
        self.assertEqual(written["embedding_stencil_route"], "chart_metric_derivatives_level_set")

    def test_bad_normal_or_forbidden_flag_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "chart.json"
            bad = _input()
            bad["normal_norm_sign"] = -1.0
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("normal sign", payload["validation_error"])

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "chart.json"
            bad = _input()
            bad["compressed_planck_lcdm_background_used"] = True
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("compressed_planck_lcdm_background_used", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
