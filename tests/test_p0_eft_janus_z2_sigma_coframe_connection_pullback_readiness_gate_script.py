import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_coframe_connection_pullback_readiness_gate import (
    build_payload,
)
from tests.test_z2_sigma_embedding_geometry_manifest import _manifest


class P0EFTJanusZ2SigmaCoframeConnectionPullbackReadinessGateTests(unittest.TestCase):
    def test_standard_pullback_formulae_are_closed(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["coframe_connection_pullback_readiness_ledger_declared"])
        self.assertTrue(payload["readiness"]["differential_form_pullback_ready"])
        self.assertTrue(payload["readiness"]["coframe_pullback_formula_ready"])
        self.assertTrue(payload["readiness"]["spin_connection_pullback_formula_ready"])

    def test_local_components_manifest_unblocks_actual_pullbacks(self):
        payload = build_payload()

        self.assertFalse(payload["readiness"]["active_embedding_ready"])
        self.assertFalse(payload["readiness"]["tangent_frame_ready"])
        self.assertTrue(payload["readiness"]["coframe_pullback_ready"])
        self.assertTrue(payload["readiness"]["spin_connection_pullback_ready"])
        self.assertFalse(payload["upstream_frontiers"]["active_embedding"]["ready"])
        self.assertFalse(payload["upstream_frontiers"]["tangent_normal_orientation"]["ready"])
        self.assertTrue(
            payload["upstream_frontiers"]["coframe_connection_components_manifest"]["valid"]
        )
        self.assertFalse(payload["coframe_connection_pullback_readiness_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")

    def test_valid_active_embedding_manifest_unblocks_pullback_readiness(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")

            payload = build_payload(embedding_manifest_path=path)

        self.assertTrue(payload["upstream_frontiers"]["active_embedding_geometry_manifest"]["valid"])
        self.assertTrue(payload["readiness"]["active_embedding_ready"])
        self.assertTrue(payload["readiness"]["tangent_frame_ready"])
        self.assertTrue(payload["readiness"]["normal_orientation_ready"])
        self.assertTrue(payload["coframe_connection_pullback_readiness_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")


if __name__ == "__main__":
    unittest.main()
