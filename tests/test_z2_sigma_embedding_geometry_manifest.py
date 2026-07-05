import json
import tempfile
import unittest
from pathlib import Path

from janus_lab.z2_sigma_embedding_geometry_manifest import (
    load_active_z2sigma_embedding_geometry_manifest,
)


def _manifest() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.5, 1.0],
        "R_Sigma_of_a": [1.0, 1.1],
        "X_plus_of_a": [[[1.0]], [[1.1]]],
        "X_minus_of_a": [[[-1.0]], [[-1.1]]],
        "tangent_frames_plus": [[[1.0]], [[1.0]]],
        "tangent_frames_minus": [[[-1.0]], [[-1.0]]],
        "unit_normals_plus": [[[1.0]], [[1.0]]],
        "unit_normals_minus": [[[-1.0]], [[-1.0]]],
        "christoffels_plus": [[[0.0]], [[0.0]]],
        "christoffels_minus": [[[0.0]], [[0.0]]],
        "spatial_inverse_metric": [[[1.0]], [[1.0]]],
        "z2_orientation_sign": 1.0,
        "embedding_provenance": "active_RSigma_solution_certificate",
    }


class Z2SigmaEmbeddingGeometryManifestTests(unittest.TestCase):
    def test_valid_manifest_loads(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")

            payload = load_active_z2sigma_embedding_geometry_manifest(path)

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["R_Sigma_of_a"], [1.0, 1.1])

    def test_forbidden_or_shape_bad_manifest_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            payload = _manifest()
            payload["archived_z4_background_reuse_used"] = True
            path.write_text(json.dumps(payload), encoding="utf-8")

            with self.assertRaises(ValueError):
                load_active_z2sigma_embedding_geometry_manifest(path)


if __name__ == "__main__":
    unittest.main()
