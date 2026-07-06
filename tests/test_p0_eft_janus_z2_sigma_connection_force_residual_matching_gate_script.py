from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_connection_force_residual_matching_gate import (
    build_payload,
    render_markdown,
)
from tests.test_z2_sigma_embedding_geometry_manifest import _manifest


class ConnectionForceResidualMatchingGateTests(unittest.TestCase):
    def test_target_written_but_default_split_blocks_matching(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["target_ready"])
        self.assertFalse(payload["matching_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "determinant_gradient_split_ready")

    def test_embedding_manifest_moves_blocker_to_source_force_equations(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")

            payload = build_payload(embedding_manifest_path=path)

        self.assertTrue(payload["closure"]["determinant_gradient_split_ready"])
        self.assertEqual(payload["primary_blocker"], "source_force_equations_derived")
        self.assertFalse(payload["closure"]["plus_connection_force_matched"])
        self.assertFalse(payload["closure"]["feeds_plus_transport_compatibility"])

    def test_forbidden_shortcuts_keep_connection_force_explicit(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_shortcuts"])

        self.assertIn("C.K connection-force", forbidden)
        self.assertIn("determinant gradients", forbidden)
        self.assertIn("Q_cross", forbidden)

    def test_markdown_reports_source_open_matching(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Connection-Force Residual Matching", markdown)
        self.assertIn("Gate passed: `False`", markdown)
        self.assertIn("force equations are not yet source-derived", markdown)


if __name__ == "__main__":
    unittest.main()
