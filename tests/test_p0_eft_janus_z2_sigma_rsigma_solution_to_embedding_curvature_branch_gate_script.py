import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rsigma_solution_to_embedding_curvature_branch_gate import (
    REQUIRED_CERTIFICATE_FIELDS,
    build_payload,
)


def _closed_frontier() -> dict:
    return {
        "status": "janus-z2-sigma-throat-radius-solution-frontier-gate",
        "status_flags": {
            "matter_flux_block_reduced": True,
            "counterterm_block_reduced": True,
            "R_Sigma_of_a_ready": True,
        },
        "throat_radius_solution_certificate_ready": True,
        "embedding_unblocked_by_radius_solution": True,
    }


def _certificate() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "effective_RSigma_equation": (
            "E_RSigma(a) := E_CartanGHY(a) + E_HolstNiehYan(a) "
            "+ E_matterFlux(a) + E_counterterm(a) = 0"
        ),
        "R_Sigma_solution_certificate_type": "conditional_closed_frontier_solution",
        "R_Sigma_solution_residual_max_abs": 0.0,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.5, 1.0],
        "R_Sigma_of_a": [1.0, 1.1],
        "X_plus_of_a": [[[1.0]], [[1.1]]],
        "X_minus_of_a": [[[-1.0]], [[-1.1]]],
        "R_curv_Z2Sigma_Mpc": 3000.0,
        "k_Z2Sigma": 1,
        "H0_Z2Sigma_km_s_Mpc": 70.0,
        "tangent_frames_plus": [[[1.0]], [[1.0]]],
        "tangent_frames_minus": [[[-1.0]], [[-1.0]]],
        "unit_normals_plus": [[[1.0]], [[1.0]]],
        "unit_normals_minus": [[[-1.0]], [[-1.0]]],
        "christoffels_plus": [[[0.0]], [[0.0]]],
        "christoffels_minus": [[[0.0]], [[0.0]]],
        "spatial_inverse_metric": [[[1.0]], [[1.0]]],
        "z2_orientation_sign": 1.0,
        "rsigma_solution_provenance": "active no-fit throat radius solution",
    }


class RSigmaSolutionToEmbeddingCurvatureBranchGateTests(unittest.TestCase):
    def test_missing_certificate_blocks_bridge(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["primary_blocker"],
            "R_Sigma_solution_certificate_from_coupled_radius_flux_system",
        )
        self.assertTrue(payload["bridge_declared"])
        self.assertFalse(payload["throat_radius_frontier_ready"])
        self.assertFalse(payload["would_write_embedding_manifest"])

    def test_complete_certificate_still_blocks_until_throat_frontier_closes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cert = root / "rsigma.json"
            cert.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_background_reuse_used": False,
                        "observational_H0_fit_used": False,
                        "observational_curvature_fit_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        **{field: [] for field in REQUIRED_CERTIFICATE_FIELDS},
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=cert)

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["throat_radius_frontier"]["matter_flux_block_reduced"])
        self.assertFalse(payload["throat_radius_frontier"]["counterterm_block_reduced"])
        self.assertFalse(
            payload["throat_radius_frontier"]["throat_radius_solution_certificate_ready"]
        )
        self.assertFalse(
            payload["throat_radius_frontier"]["embedding_unblocked_by_radius_solution"]
        )
        self.assertEqual(payload["input_certificate"]["missing_fields"], [])

    def test_closed_frontier_and_certificate_write_embedding_and_curvature_manifests(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cert = root / "rsigma.json"
            embedding = root / "embedding.json"
            curvature = root / "curvature.json"
            h0_norm = root / "h0_norm.json"
            radius_norm = root / "radius_norm.json"
            cert.write_text(json.dumps(_certificate()), encoding="utf-8")

            payload = build_payload(
                input_path=cert,
                embedding_output_path=embedding,
                curvature_output_path=curvature,
                h0_normalization_output_path=h0_norm,
                curvature_radius_normalization_output_path=radius_norm,
                frontier_payload=_closed_frontier(),
            )
            embedding_payload = json.loads(embedding.read_text(encoding="utf-8"))
            curvature_payload = json.loads(curvature.read_text(encoding="utf-8"))
            h0_payload = json.loads(h0_norm.read_text(encoding="utf-8"))
            radius_payload = json.loads(radius_norm.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertTrue(payload["embedding_manifest_written"])
        self.assertTrue(payload["curvature_branch_manifest_written"])
        self.assertTrue(payload["h0_normalization_manifest_written"])
        self.assertTrue(payload["curvature_radius_normalization_manifest_written"])
        self.assertEqual(embedding_payload["embedding_provenance"], "active no-fit throat radius solution")
        self.assertIn("E_RSigma", embedding_payload["effective_RSigma_equation"])
        self.assertEqual(curvature_payload["scalars"]["R_curv_Z2Sigma_Mpc"], 3000.0)
        self.assertIn("E_RSigma", curvature_payload["source_effective_RSigma_equation"])
        self.assertEqual(h0_payload["scalars"]["H0_Z2Sigma_km_s_Mpc"], 70.0)
        self.assertIn("E_RSigma", h0_payload["source_effective_RSigma_equation"])
        self.assertEqual(radius_payload["scalars"]["R_curv_Z2Sigma_Mpc"], 3000.0)
        self.assertIn("E_RSigma", radius_payload["source_effective_RSigma_equation"])
        self.assertFalse(h0_payload["observational_H0_fit_used"])
        self.assertFalse(curvature_payload["observational_curvature_fit_used"])

    def test_closed_frontier_rejects_invalid_certificate(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cert = root / "rsigma.json"
            bad = _certificate()
            bad["compressed_planck_lcdm_background_used"] = True
            cert.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=cert, frontier_payload=_closed_frontier())

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["would_write_embedding_manifest"])
        self.assertIn("Forbidden provenance flag", payload["input_certificate"]["validation_error"])

    def test_closed_frontier_rejects_certificate_without_effective_equation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cert = root / "rsigma.json"
            bad = _certificate()
            bad["effective_RSigma_equation"] = "R(a)=constant"
            cert.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=cert, frontier_payload=_closed_frontier())

        self.assertFalse(payload["gate_passed"])
        self.assertIn("E_RSigma", payload["input_certificate"]["validation_error"])


if __name__ == "__main__":
    unittest.main()
