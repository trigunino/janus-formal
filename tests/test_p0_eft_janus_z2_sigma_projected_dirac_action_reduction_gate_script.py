import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_action_reduction_gate import build_payload
from tests.test_z2_sigma_embedding_geometry_manifest import _manifest


class P0EFTJanusZ2SigmaProjectedDiracActionReductionGateTests(unittest.TestCase):
    def test_projected_dirac_action_reduction_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["projected_dirac_action_reduction_ledger_declared"])
        self.assertTrue(payload["declared"]["coframe_connection_pullback_gate_declared"])
        self.assertTrue(payload["declared"]["spinor_bundle_projection_gate_declared"])
        self.assertTrue(payload["declared"]["no_effective_fitted_mass_or_phase"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertTrue(payload["local_projected_dirac_action_reduction_ready"])
        self.assertFalse(payload["strict_full_embedding_projected_dirac_action_ready"])

    def test_reduction_waits_for_pullback_and_projection(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["coframe_connection_pullback_ready"])
        self.assertTrue(payload["closure"]["plus_minus_spinor_projection_ready"])
        self.assertTrue(payload["closure"]["Z2_projected_Dirac_action_ready"])
        self.assertTrue(payload["projected_dirac_action_reduction_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertIn("coframe_connection_pullback", payload["upstream_frontiers"])
        self.assertIn("spinor_bundle_projection", payload["upstream_frontiers"])
        self.assertTrue(
            payload["upstream_frontiers"]["coframe_connection_pullback"][
                "strict_full_embedding_not_claimed"
            ]
        )
        self.assertIn("feed_projected_action_to_mass_term_from_action_gate", payload["next_required"])

    def test_valid_embedding_manifest_unblocks_only_coframe_frontier(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")

            payload = build_payload(embedding_manifest_path=path)

        self.assertTrue(payload["closure"]["coframe_connection_pullback_ready"])
        self.assertTrue(payload["closure"]["plus_minus_spinor_projection_ready"])
        self.assertTrue(payload["closure"]["Z2_projected_Dirac_action_ready"])
        self.assertTrue(payload["projected_dirac_action_reduction_ready"])
        self.assertEqual(payload["primary_blocker"], "none")


if __name__ == "__main__":
    unittest.main()
