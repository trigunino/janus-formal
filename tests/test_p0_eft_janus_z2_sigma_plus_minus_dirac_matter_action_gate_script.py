import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_plus_minus_dirac_matter_action_gate import build_payload
from tests.test_z2_sigma_embedding_geometry_manifest import _manifest


class P0EFTJanusZ2SigmaPlusMinusDiracMatterActionGateTests(unittest.TestCase):
    def test_dirac_matter_action_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["plus_minus_dirac_matter_action_ledger_declared"])
        self.assertTrue(payload["declared"]["curved_Dirac_action_bibliography_checked"])
        self.assertTrue(payload["declared"]["Holst_fermion_bibliography_checked"])
        self.assertTrue(payload["declared"]["spinor_bundle_projection_gate_declared"])
        self.assertTrue(payload["declared"]["projected_Dirac_action_reduction_gate_declared"])
        self.assertTrue(payload["declared"]["plus_Dirac_action_declared"])
        self.assertTrue(payload["declared"]["minus_Dirac_action_declared"])

    def test_actions_wait_for_pullback_and_spinor_data(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["coframe_connection_pullback_ready"])
        self.assertTrue(payload["closure"]["plus_spinor_data_ready"])
        self.assertTrue(payload["closure"]["plus_minus_matter_actions_ready"])
        self.assertTrue(payload["plus_minus_dirac_matter_action_ready"])
        self.assertTrue(payload["local_plus_minus_dirac_matter_action_ready"])
        self.assertFalse(payload["strict_full_embedding_dirac_matter_action_ready"])
        self.assertIn("feed_actions_to_plus_minus_Dirac_action_local_reduction_gate", payload["next_required"])

    def test_valid_embedding_manifest_unblocks_coframe_but_not_spinor_projection(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")

            payload = build_payload(embedding_manifest_path=path)

        self.assertTrue(payload["closure"]["coframe_connection_pullback_ready"])
        self.assertTrue(payload["closure"]["plus_spinor_data_ready"])
        self.assertTrue(payload["closure"]["plus_matter_action_ready"])
        self.assertEqual(payload["primary_blocker"], "none")


if __name__ == "__main__":
    unittest.main()
