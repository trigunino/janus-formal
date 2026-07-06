import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_active_first_action_assembly_gate import (
    build_payload,
)
from tests.test_z2_sigma_embedding_geometry_manifest import _manifest


class ActiveFirstActionAssemblyGateTests(unittest.TestCase):
    def test_action_skeleton_is_declared_without_z4_reuse(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["declared_action_layer_ready"])
        self.assertFalse(payload["z4_policy"]["Z4_action_reuse_used"])
        self.assertFalse(payload["z4_policy"]["Z4_can_close_active_action"])
        self.assertTrue(payload["closure"]["Z4_action_reuse_forbidden"])
        self.assertIn("S_active", payload["action_formula"])

    def test_action_contains_expected_active_terms(self):
        payload = build_payload()
        terms = payload["terms"]

        self.assertIn("S_grav_plus", terms)
        self.assertIn("S_grav_minus", terms)
        self.assertIn("S_Sigma", terms)
        self.assertIn("S_matter_plus", terms)
        self.assertIn("S_matter_minus", terms)
        self.assertIn("S_ct", terms)
        self.assertIn("S_cross_transport", terms)

    def test_current_blocker_is_cross_action_after_local_matter_closure(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "cross_action_source_accepted")
        self.assertIn("cross_action_source_accepted", payload["blockers"])
        self.assertTrue(payload["upstream"]["matter_action"]["ready"])
        self.assertFalse(payload["upstream"]["cross_action"]["source_accepted"])

    def test_embedding_manifest_keeps_action_blocker_on_cross_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")

            payload = build_payload(embedding_manifest_path=path)

        self.assertEqual(payload["primary_blocker"], "cross_action_source_accepted")
        self.assertEqual(payload["upstream"]["matter_action"]["primary_blockers"], [])

    def test_counterterm_boundary_functional_can_be_closed_without_density_inputs(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["counterterm_boundary_action_closed"])
        self.assertFalse(payload["upstream"]["counterterm"]["density_inputs_allowed"])


if __name__ == "__main__":
    unittest.main()
