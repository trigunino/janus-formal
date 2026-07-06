import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_transport_map_derivation_gate import build_payload
from tests.test_z2_sigma_embedding_geometry_manifest import _manifest


class TransportMapDerivationGateTests(unittest.TestCase):
    def test_transport_maps_are_declared_but_source_derivation_is_open(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["declared_transport_layer_ready"])
        self.assertFalse(payload["source_derivation_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["route_status"],
            "declared_waiting_for_active_embedding_and_source_compatibility",
        )
        self.assertIn("bridge_maps_source_derived", payload["blockers"])

    def test_same_bridge_feeds_stress_and_qcross(self):
        payload = build_payload()
        maps = payload["transport_maps"]
        closure = payload["closure"]

        self.assertIn("M_-+", maps["M_minus_to_plus"])
        self.assertIn("M_+-", maps["M_plus_to_minus"])
        self.assertIn("same M_minus_to_plus", maps["Q_cross"])
        self.assertTrue(closure["stress_transport_uses_bridge"])
        self.assertTrue(closure["Q_cross_uses_same_bridge"])
        self.assertTrue(closure["determinant_factors_kept_separate"])
        self.assertTrue(closure["no_independent_optical_transport"])

    def test_feeds_bianchi_but_does_not_remove_source_blocker_yet(self):
        payload = build_payload()

        self.assertTrue(payload["feeds_bianchi_gate"]["formal_bianchi_closed"])
        self.assertFalse(payload["feeds_bianchi_gate"]["can_remove_bianchi_source_blocker"])
        self.assertIn("prove_plus_transport_compatibility", " ".join(payload["next_required"]))

    def test_active_embedding_manifest_derives_bridge_maps_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")

            payload = build_payload(embedding_manifest_path=path)

        self.assertTrue(payload["upstream_embedding_readiness"]["active_embedding_ready"])
        self.assertTrue(payload["closure"]["bridge_maps_source_derived"])
        self.assertTrue(payload["bridge_map_source_derivation"]["ready"])
        self.assertFalse(payload["closure"]["plus_transport_compatibility_source_derived"])
        self.assertFalse(payload["closure"]["minus_transport_compatibility_source_derived"])
        self.assertFalse(payload["source_derivation_ready"])
        self.assertEqual(payload["primary_blocker"], "plus_transport_compatibility_source_derived")


if __name__ == "__main__":
    unittest.main()
