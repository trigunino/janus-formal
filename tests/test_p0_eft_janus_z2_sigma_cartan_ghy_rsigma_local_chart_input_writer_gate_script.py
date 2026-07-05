import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_local_chart_input_writer_gate import (
    build_payload,
)


def _input() -> dict:
    radial_offsets = [-0.1, 0.0, 0.1]
    ambient_offsets = [
        [0.0, 0.0],
        [-0.1, 0.0],
        [0.1, 0.0],
        [0.0, -0.1],
        [0.0, 0.1],
        [0.1, 0.1],
    ]
    intrinsic_offsets = [[-0.1], [0.0], [0.1]]
    bases = [2.0, 3.0]
    metric_samples = []
    level_samples = []
    embedding_samples = []
    for base in bases:
        metric_radial = []
        level_radial = []
        embedding_radial = []
        for radial in radial_offsets:
            radius0 = base + radial
            metric_row = []
            level_row = []
            for ambient in ambient_offsets:
                radius = radius0 + ambient[0]
                metric_row.append([[1.0, 0.0], [0.0, radius * radius]])
                level_row.append(ambient[0])
            embedding_row = []
            for intrinsic in intrinsic_offsets:
                embedding_row.append([radius0, intrinsic[0]])
            metric_radial.append(metric_row)
            level_radial.append(level_row)
            embedding_radial.append(embedding_row)
        metric_samples.append(metric_radial)
        level_samples.append(level_radial)
        embedding_samples.append(embedding_radial)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.5, 1.0],
        "radial_offsets": radial_offsets,
        "ambient_coordinate_offsets": ambient_offsets,
        "intrinsic_coordinate_offsets": intrinsic_offsets,
        "metric_covariant_samples": metric_samples,
        "level_set_samples": level_samples,
        "embedding_coordinate_samples": embedding_samples,
        "normal_norm_sign": 1.0,
        "orientation_sign": 1.0,
        "z2_orientation_sign": 1.0,
        "kappa_Z2Sigma": 2.0,
        "E_CartanGHY_provenance": "active Cartan-GHY sampled local chart",
    }


class CartanGHYRSigmaLocalChartInputWriterGateTests(unittest.TestCase):
    def test_local_chart_samples_write_chart_stencil(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "local_chart.json"
            output_path = root / "chart_stencil.json"
            input_path.write_text(json.dumps(_input()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertAlmostEqual(written["metric_covariant_stencil"][0][1][1][1], 4.0)
        self.assertAlmostEqual(written["metric_derivatives_stencil"][0][1][0][1][1], 4.0)
        self.assertAlmostEqual(written["tangent_vectors_stencil"][0][1][0][1], 1.0)
        self.assertAlmostEqual(written["second_embedding_stencil"][0][1][0][0][0], 0.0)
        self.assertAlmostEqual(written["level_gradient_covector_stencil"][0][1][0], 1.0)

    def test_rank_failure_or_forbidden_flag_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "local_chart.json"
            bad = _input()
            bad["intrinsic_coordinate_offsets"] = [[0.0], [0.1]]
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("embedding_coordinate_samples", payload["validation_error"])

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "local_chart.json"
            bad = _input()
            bad["phenomenological_holst_bao_scan_used"] = True
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("phenomenological_holst_bao_scan_used", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
