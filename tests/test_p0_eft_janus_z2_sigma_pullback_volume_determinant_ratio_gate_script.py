from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_pullback_volume_determinant_ratio_gate import (
    build_payload,
    render_markdown,
)
from tests.test_z2_sigma_embedding_geometry_manifest import _manifest


class PullbackVolumeDeterminantRatioGateTests(unittest.TestCase):
    def test_template_ready_but_default_embedding_blocks_derivation(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["template_ready"])
        self.assertFalse(payload["derivation_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "active_embedding_ready")

    def test_embedding_manifest_derives_b_factors(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")

            payload = build_payload(embedding_manifest_path=path)

        self.assertTrue(payload["derivation_ready"])
        self.assertTrue(payload["closure"]["B_plus_from_pullback_volume"])
        self.assertTrue(payload["closure"]["B_minus_from_inverse_pullback_volume"])
        self.assertTrue(payload["closure"]["reciprocal_identity_derived"])
        self.assertTrue(payload["closure"]["feeds_bridge_determinant_audit"])

    def test_markdown_mentions_no_fit_pullback_route(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Pullback Volume Determinant Ratio", markdown)
        self.assertIn("Gate passed: `False`", markdown)
        self.assertIn("without fitting a coefficient", markdown)


if __name__ == "__main__":
    unittest.main()
