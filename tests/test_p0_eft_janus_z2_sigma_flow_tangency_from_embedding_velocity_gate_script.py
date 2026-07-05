import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_flow_tangency_from_embedding_velocity_gate import (
    build_payload,
)


def _base_payload(**extra):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "a_grid": [0.5, 1.0],
    }
    payload.update(extra)
    return payload


class P0EFTJanusZ2SigmaFlowTangencyFromEmbeddingVelocityGateTests(unittest.TestCase):
    def test_missing_inputs_keep_gate_blocked(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                metric_path=root / "missing_metric.json",
                velocity_path=root / "missing_velocity.json",
                embedding_path=root / "missing_embedding.json",
                unit_frame_path=root / "missing_frame.json",
                output_path=root / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("sector_metric_on_sigma_inputs", payload["input_exists"])

    def test_gate_writes_when_u_and_tangents_are_normal_orthogonal(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            metric = root / "metric.json"
            velocity = root / "velocity.json"
            embedding = root / "embedding.json"
            output = root / "out.json"
            metric.write_text(
                json.dumps(
                    _base_payload(
                        sector_metric_on_sigma_ready=True,
                        metric_plus_munu_values=[[[-1.0, 0.0], [0.0, 1.0]]] * 2,
                        metric_minus_munu_values=[[[-1.0, 0.0], [0.0, 1.0]]] * 2,
                    )
                ),
                encoding="utf-8",
            )
            velocity.write_text(
                json.dumps(
                    _base_payload(
                        sector_four_velocity_on_sigma_ready=True,
                        u_plus_contravariant_values=[[1.0, 0.0], [1.0, 0.0]],
                        u_minus_contravariant_values=[[1.0, 0.0], [1.0, 0.0]],
                    )
                ),
                encoding="utf-8",
            )
            embedding.write_text(
                json.dumps(
                    _base_payload(
                        R_Sigma_of_a=[1.0, 1.0],
                        X_plus_of_a=[[0.0, 1.0], [0.0, 1.0]],
                        X_minus_of_a=[[0.0, 1.0], [0.0, 1.0]],
                        tangent_frames_plus=[[[1.0, 0.0]], [[1.0, 0.0]]],
                        tangent_frames_minus=[[[1.0, 0.0]], [[1.0, 0.0]]],
                        unit_normals_plus=[[0.0, 1.0], [0.0, 1.0]],
                        unit_normals_minus=[[0.0, -1.0], [0.0, -1.0]],
                        christoffels_plus=[[[0.0]], [[0.0]]],
                        christoffels_minus=[[[0.0]], [[0.0]]],
                        spatial_inverse_metric=[[[1.0]], [[1.0]]],
                        z2_orientation_sign=-1.0,
                        embedding_provenance="unit-test-active-derived",
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                metric_path=metric,
                velocity_path=velocity,
                embedding_path=embedding,
                output_path=output,
            )

        self.assertTrue(payload["flow_tangency_written"])
        self.assertTrue(payload["flow_tangency_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")

    def test_gate_accepts_unit_frame_without_full_embedding(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            metric = root / "metric.json"
            velocity = root / "velocity.json"
            unit_frame = root / "frame.json"
            output = root / "out.json"
            metric.write_text(
                json.dumps(
                    _base_payload(
                        sector_metric_on_sigma_ready=True,
                        metric_plus_munu_values=[[[-1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]]] * 2,
                        metric_minus_munu_values=[[[-1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]]] * 2,
                    )
                ),
                encoding="utf-8",
            )
            velocity.write_text(
                json.dumps(
                    _base_payload(
                        sector_four_velocity_on_sigma_ready=True,
                        u_plus_contravariant_values=[[1.0, 0.0, 0.0], [1.0, 0.0, 0.0]],
                        u_minus_contravariant_values=[[1.0, 0.0, 0.0], [1.0, 0.0, 0.0]],
                    )
                ),
                encoding="utf-8",
            )
            unit_frame.write_text(
                json.dumps(
                    _base_payload(
                        sigma_unit_frame_ready=True,
                        tangent_frames_plus=[[[1.0, 0.0, 0.0]], [[1.0, 0.0, 0.0]]],
                        tangent_frames_minus=[[[1.0, 0.0, 0.0]], [[1.0, 0.0, 0.0]]],
                        unit_normals_plus=[[0.0, 0.0, 1.0], [0.0, 0.0, 1.0]],
                        unit_normals_minus=[[0.0, 0.0, -1.0], [0.0, 0.0, -1.0]],
                        frame_provenance="unit-test-local-frame",
                        full_embedding_claimed=False,
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                metric_path=metric,
                velocity_path=velocity,
                embedding_path=root / "missing_embedding.json",
                unit_frame_path=unit_frame,
                output_path=output,
            )
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["frame_source"], "sigma_unit_frame_inputs")
        self.assertFalse(written["full_embedding_claimed"])


if __name__ == "__main__":
    unittest.main()
