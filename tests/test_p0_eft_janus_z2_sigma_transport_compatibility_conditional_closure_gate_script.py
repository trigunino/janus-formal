import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_transport_compatibility_conditional_closure_gate import (
    build_payload,
)
from tests.test_z2_sigma_embedding_geometry_manifest import _manifest


class TransportCompatibilityConditionalClosureGateTests(unittest.TestCase):
    def test_conditional_layer_imports_existing_bianchi_theorem(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["declared_conditional_layer_ready"])
        self.assertTrue(payload["closure"]["same_sector_stress_conservation_gate_imported"])
        self.assertTrue(payload["closure"]["conditional_bianchi_theorem_imported"])
        self.assertTrue(payload["closure"]["connection_force_targets_imported"])
        self.assertFalse(payload["gate_passed"])

    def test_embedding_manifest_moves_blocker_to_same_sector_conservation(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")

            payload = build_payload(embedding_manifest_path=path)

        self.assertTrue(payload["closure"]["bridge_maps_source_derived"])
        self.assertEqual(payload["primary_blocker"], "same_sector_plus_stress_conserved")
        self.assertEqual(
            payload["upstream_same_sector_stress_conservation_gate"]["primary_blocker"],
            "plus_matter_action_ready",
        )

    def test_sufficient_conditions_include_continuity_and_force_targets(self):
        payload = build_payload()
        conditions = payload["sufficient_conditions"]

        self.assertIn("D_minus_nu(rho_minus u_{-to+}^nu)=0", conditions["continuity_targets"])
        self.assertIn("D_plus_nu(rho_plus u_{+to-}^nu)=0", conditions["continuity_targets"])
        self.assertTrue(any("C^mu" in item for item in conditions["force_targets"]))
        self.assertTrue(any("therefore R_plus" in item for item in conditions["positive"]))
        self.assertTrue(any("therefore R_minus" in item for item in conditions["negative"]))


if __name__ == "__main__":
    unittest.main()
