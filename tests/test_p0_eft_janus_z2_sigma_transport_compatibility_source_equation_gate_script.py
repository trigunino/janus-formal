import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_transport_compatibility_source_equation_gate import (
    build_payload,
)
from tests.test_z2_sigma_embedding_geometry_manifest import _manifest


class TransportCompatibilitySourceEquationGateTests(unittest.TestCase):
    def test_source_equation_layer_is_declared_but_open(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["declared_source_equation_layer_ready"])
        self.assertFalse(payload["source_derivation_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "bridge_maps_source_derived")

    def test_embedding_manifest_moves_blocker_to_plus_divergence(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")

            payload = build_payload(embedding_manifest_path=path)

        self.assertTrue(payload["closure"]["bridge_maps_source_derived"])
        self.assertEqual(payload["primary_blocker"], "plus_source_divergence_equation_derived")
        self.assertFalse(payload["closure"]["plus_transport_compatibility_source_derived"])
        self.assertFalse(payload["closure"]["minus_transport_compatibility_source_derived"])

    def test_definitions_keep_same_bridge_and_determinants_separate(self):
        payload = build_payload()

        self.assertIn("M_-+", payload["definitions"]["S_plus"])
        self.assertIn("M_+-", payload["definitions"]["S_minus"])
        self.assertTrue(payload["closure"]["same_bridge_used_in_both_divergences"])
        self.assertTrue(payload["closure"]["determinant_factors_kept_outside_bridge"])


if __name__ == "__main__":
    unittest.main()
