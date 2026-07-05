import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_projection_components_from_embedding_stress_gate import (
    build_payload,
)


def _base():
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
    }


def _embedding():
    payload = _base()
    payload.update(
        {
            "a_grid": [0.5, 1.0],
            "R_Sigma_of_a": [2.0, 3.0],
            "X_plus_of_a": [[[2.0, 0.0]], [[3.0, 0.0]]],
            "X_minus_of_a": [[[-2.0, 0.0]], [[-3.0, 0.0]]],
            "tangent_frames_plus": [[[1.0, 0.0]], [[0.0, 1.0]]],
            "tangent_frames_minus": [[[-1.0, 0.0]], [[0.0, -1.0]]],
            "unit_normals_plus": [[0.0, 1.0], [1.0, 0.0]],
            "unit_normals_minus": [[1.0, 0.0], [0.0, 1.0]],
            "christoffels_plus": [[[0.0, 0.0], [0.0, 0.0]], [[0.0, 0.0], [0.0, 0.0]]],
            "christoffels_minus": [[[0.0, 0.0], [0.0, 0.0]], [[0.0, 0.0], [0.0, 0.0]]],
            "spatial_inverse_metric": [[[1.0, 0.0], [0.0, 1.0]], [[1.0, 0.0], [0.0, 1.0]]],
            "z2_orientation_sign": -1.0,
            "embedding_provenance": "active_RSigma_solution_certificate",
        }
    )
    return payload


def _stress():
    payload = _base()
    payload.update(
        {
            "a_grid": [0.5, 1.0],
            "T_plus_munu_values": [
                [[2.0, 3.0], [5.0, 7.0]],
                [[11.0, 13.0], [17.0, 19.0]],
            ],
            "T_minus_munu_values": [
                [[1.0, 2.0], [3.0, 4.0]],
                [[5.0, 6.0], [7.0, 8.0]],
            ],
        }
    )
    return payload


def _radial_weights():
    payload = _base()
    payload.update(
        {
            "a_grid": [0.5, 1.0],
            "radial_variation_tangent_weights": [[2.0], [3.0]],
        }
    )
    return payload


class MatterFluxProjectionComponentsFromEmbeddingStressGateTests(unittest.TestCase):
    def test_writes_projection_components_from_primitive_manifests(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            embedding = root / "embedding.json"
            stress = root / "stress.json"
            radial = root / "radial.json"
            output = root / "projection.json"
            embedding.write_text(json.dumps(_embedding()), encoding="utf-8")
            stress.write_text(json.dumps(_stress()), encoding="utf-8")
            radial.write_text(json.dumps(_radial_weights()), encoding="utf-8")

            payload = build_payload(
                embedding_path=embedding,
                stress_path=stress,
                radial_weights_path=radial,
                output_path=output,
            )
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["projection_components_ready"])
        self.assertEqual(written["eps_Z2"], -1.0)
        self.assertEqual(written["tangent_vectors_values"], [[[1.0, 0.0]], [[0.0, 1.0]]])
        self.assertEqual(written["normal_plus_values"], [[0.0, 1.0], [1.0, 0.0]])
        self.assertEqual(written["radial_variation_tangent_weights"], [[2.0], [3.0]])

    def test_missing_stress_reports_exact_blocker(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            embedding = root / "embedding.json"
            radial = root / "radial.json"
            embedding.write_text(json.dumps(_embedding()), encoding="utf-8")
            radial.write_text(json.dumps(_radial_weights()), encoding="utf-8")

            payload = build_payload(
                embedding_path=embedding,
                stress_path=root / "missing.json",
                radial_weights_path=radial,
                output_path=root / "projection.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "bulk_stress_on_sigma_inputs")

    def test_forbidden_stress_provenance_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            embedding = root / "embedding.json"
            stress = root / "stress.json"
            radial = root / "radial.json"
            embedding.write_text(json.dumps(_embedding()), encoding="utf-8")
            bad = _stress()
            bad["observational_H0_fit_used"] = True
            stress.write_text(json.dumps(bad), encoding="utf-8")
            radial.write_text(json.dumps(_radial_weights()), encoding="utf-8")

            payload = build_payload(
                embedding_path=embedding,
                stress_path=stress,
                radial_weights_path=radial,
                output_path=root / "projection.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
