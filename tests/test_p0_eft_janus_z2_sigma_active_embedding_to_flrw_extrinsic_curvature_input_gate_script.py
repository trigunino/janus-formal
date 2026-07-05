import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_to_flrw_extrinsic_curvature_input_gate import (
    REQUIRED_FIELDS,
    build_payload,
)


def _embedding_manifest(*, include_k: bool = False) -> dict:
    payload = {
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
    if include_k:
        payload.update(
            {
                "K_s_plus_Z2Sigma": [3.0, 6.0],
                "K_s_minus_Z2Sigma": [1.0, 2.0],
                "K_tau_plus_Z2Sigma": [5.0, 10.0],
                "K_tau_minus_Z2Sigma": [2.0, 4.0],
                "K_provenance": "active embedding second fundamental form reduction",
            }
        )
    return payload


def _embedding_manifest_with_second_form() -> dict:
    payload = _embedding_manifest()
    payload.update(
        {
            "X_plus_of_a": [[0.0, 1.0, 0.0, 0.0], [0.0, 2.0, 0.0, 0.0]],
            "X_minus_of_a": [[0.0, -1.0, 0.0, 0.0], [0.0, -2.0, 0.0, 0.0]],
            "tangent_frames_plus": [[[1.0, 0.0, 0.0, 0.0],
                                      [0.0, 1.0, 0.0, 0.0],
                                      [0.0, 0.0, 1.0, 0.0],
                                      [0.0, 0.0, 0.0, 1.0]]
                                     for _ in payload["a_grid"]],
            "tangent_frames_minus": [[[1.0, 0.0, 0.0, 0.0],
                                       [0.0, 1.0, 0.0, 0.0],
                                       [0.0, 0.0, 1.0, 0.0],
                                       [0.0, 0.0, 0.0, 1.0]]
                                      for _ in payload["a_grid"]],
            "unit_normals_plus": [[1.0, 0.0, 0.0, 0.0] for _ in payload["a_grid"]],
            "unit_normals_minus": [[1.0, 0.0, 0.0, 0.0] for _ in payload["a_grid"]],
            "christoffels_plus": [[[[0.0 for _ in range(4)] for _ in range(4)] for _ in range(4)]
                                  for _ in payload["a_grid"]],
            "christoffels_minus": [[[[0.0 for _ in range(4)] for _ in range(4)] for _ in range(4)]
                                   for _ in payload["a_grid"]],
            "spatial_inverse_metric": [[[1.0, 0.0, 0.0],
                                        [0.0, 0.5, 0.0],
                                        [0.0, 0.0, 1.0 / 3.0]]
                                       for _ in payload["a_grid"]],
            "second_embedding_plus": [],
            "second_embedding_minus": [],
            "embedding_provenance": "active second-form embedding geometry",
        }
    )
    for a in [0.5, 1.0]:
        plus = [[[0.0 for _ in range(4)] for _ in range(4)] for _ in range(4)]
        minus = [[[0.0 for _ in range(4)] for _ in range(4)] for _ in range(4)]
        plus[0][0][0] = -2.0 * a
        plus[1][1][0] = -3.0 * a
        plus[2][2][0] = -6.0 * a
        plus[3][3][0] = -9.0 * a
        minus[0][0][0] = -1.0 * a
        minus[1][1][0] = -2.0 * a
        minus[2][2][0] = -4.0 * a
        minus[3][3][0] = -6.0 * a
        payload["second_embedding_plus"].append(plus)
        payload["second_embedding_minus"].append(minus)
    return payload


class ActiveEmbeddingToFLRWExtrinsicCurvatureInputGateTests(unittest.TestCase):
    def test_missing_embedding_manifest_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertTrue(payload["adapter_declared"])
        self.assertFalse(payload["active_tunnel_embedding_of_a_closure_ready"])
        self.assertEqual(
            payload["upstream_frontiers"]["active_tunnel_embedding_of_a"]["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertIn("active_tunnel_embedding_of_a", payload["upstream_frontiers"])
        self.assertIn(
            "X_plus_minus_of_a_derived",
            payload["nearest_embedding_to_flrw_K_frontier"]["blocks"],
        )
        self.assertTrue(payload["nearest_embedding_to_flrw_K_frontier"]["diagnostic_only"])

    def test_complete_manifest_without_k_still_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "embedding.json"
            output_path = root / "flrw_extrinsic_curvature_grid_inputs.json"
            input_path.write_text(
                json.dumps(_embedding_manifest()),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(output_path.exists())
        self.assertEqual(payload["input_manifest"]["missing_fields"], [])
        self.assertIn("K_s_plus_Z2Sigma", payload["input_manifest"]["missing_k_fields"])
        self.assertIn("K_s/K_tau", payload["blocker"])
        self.assertIn(
            "K_s_plus_Z2Sigma",
            payload["nearest_embedding_to_flrw_K_frontier"]["blocks"],
        )

    def test_complete_manifest_with_k_writes_flrw_grid_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "embedding.json"
            output_path = root / "flrw_extrinsic_curvature_grid_inputs.json"
            input_path.write_text(
                json.dumps(_embedding_manifest(include_k=True)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["nearest_embedding_to_flrw_K_frontier"]["blocks"], [])
        self.assertEqual(written["K_s_plus_Z2Sigma"], [3.0, 6.0])
        self.assertFalse(written["archived_z4_reuse_used"])

    def test_complete_manifest_with_second_form_computes_flrw_grid_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "embedding.json"
            output_path = root / "flrw_extrinsic_curvature_grid_inputs.json"
            input_path.write_text(
                json.dumps(_embedding_manifest_with_second_form()),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["can_compute_K_from_second_embedding"])
        self.assertEqual(payload["K_reduction_route"], "computed_from_second_embedding")
        self.assertEqual(written["K_reduction_route"], "computed_from_second_embedding")
        self.assertEqual(written["K_s_plus_Z2Sigma"], [1.5, 3.0])
        self.assertEqual(written["K_tau_plus_Z2Sigma"], [1.0, 2.0])
        self.assertEqual(written["K_s_minus_Z2Sigma"], [1.0, 2.0])
        self.assertEqual(written["K_tau_minus_Z2Sigma"], [0.5, 1.0])

    def test_forbidden_embedding_provenance_blocks_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "embedding.json"
            bad = _embedding_manifest()
            bad["archived_z4_background_reuse_used"] = True
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance flag", payload["input_manifest"]["validation_error"])


if __name__ == "__main__":
    unittest.main()
