import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import build_payload
from tests.test_z2_sigma_embedding_geometry_manifest import _manifest


class P0EFTJanusZ2SigmaActiveEmbeddingReadinessGateTests(unittest.TestCase):
    def test_conditional_embedding_is_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["active_embedding_readiness_ledger_declared"])
        self.assertTrue(payload["readiness"]["embedding_gauge_equations_ready"])
        self.assertTrue(payload["readiness"]["conditional_radius_to_embedding_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")

    def test_active_embedding_waits_for_radius_law(self):
        payload = build_payload()

        self.assertFalse(payload["upstream_frontiers"]["active_embedding_geometry_manifest"]["exists"])
        self.assertFalse(payload["readiness"]["R_Sigma_of_a_ready"])
        self.assertFalse(payload["readiness"]["throat_radius_solution_certificate_ready"])
        self.assertFalse(payload["readiness"]["embedding_unblocked_by_radius_solution"])
        self.assertFalse(payload["readiness"]["X_plus_minus_of_a_ready"])
        self.assertTrue(payload["upstream_frontiers"]["radius_to_embedding"]["conditional_ready"])
        self.assertFalse(payload["upstream_frontiers"]["radius_to_embedding"]["unconditional_ready"])
        self.assertFalse(payload["upstream_frontiers"]["embedding_from_radius"]["ready"])
        self.assertFalse(payload["readiness"]["active_embedding_ready"])
        self.assertFalse(payload["active_embedding_readiness_ready"])
        self.assertTrue(payload["nearest_embedding_frontier_declared"])
        self.assertTrue(payload["nearest_embedding_frontier_diagnostic_only"])
        self.assertEqual(payload["nearest_embedding_frontier"]["block"], "R_Sigma_solution_certificate")
        self.assertEqual(
            payload["nearest_embedding_frontier"]["gate"],
            "P0EFTJanusZ2SigmaThroatRadiusSolutionFrontierGate",
        )
        self.assertIn(
            "solve E_RSigma(a)=0 without fit",
            payload["nearest_embedding_frontier"]["required"],
        )

    def test_valid_active_embedding_manifest_closes_readiness(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")

            payload = build_payload(embedding_manifest_path=path)

        self.assertTrue(payload["upstream_frontiers"]["active_embedding_geometry_manifest"]["valid"])
        self.assertTrue(payload["readiness"]["throat_radius_solution_certificate_ready"])
        self.assertTrue(payload["readiness"]["R_Sigma_of_a_ready"])
        self.assertTrue(payload["readiness"]["X_plus_minus_of_a_ready"])
        self.assertTrue(payload["readiness"]["tangent_frames_ready"])
        self.assertTrue(payload["readiness"]["unit_normals_ready"])
        self.assertTrue(payload["readiness"]["active_embedding_ready"])
        self.assertTrue(payload["active_embedding_readiness_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")

    def test_forbidden_embedding_manifest_does_not_close_readiness(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            manifest = _manifest()
            manifest["archived_z4_background_reuse_used"] = True
            path.write_text(json.dumps(manifest), encoding="utf-8")

            payload = build_payload(embedding_manifest_path=path)

        self.assertFalse(payload["upstream_frontiers"]["active_embedding_geometry_manifest"]["valid"])
        self.assertIn(
            "archived_z4_background_reuse_used",
            payload["upstream_frontiers"]["active_embedding_geometry_manifest"][
                "validation_error"
            ],
        )
        self.assertFalse(payload["readiness"]["active_embedding_ready"])


if __name__ == "__main__":
    unittest.main()
