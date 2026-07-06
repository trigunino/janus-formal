from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_determinant_gradient_divergence_gate import (
    build_payload,
    render_markdown,
)
from tests.test_z2_sigma_embedding_geometry_manifest import _manifest


class DeterminantGradientDivergenceGateTests(unittest.TestCase):
    def test_template_ready_but_default_b_factors_block_split(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["template_ready"])
        self.assertFalse(payload["divergence_split_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["primary_blocker"], "B_plus_from_pullback_volume_ready"
        )

    def test_embedding_manifest_closes_divergence_split(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")

            payload = build_payload(embedding_manifest_path=path)

        self.assertTrue(payload["divergence_split_ready"])
        self.assertTrue(payload["closure"]["plus_divergence_split_derived"])
        self.assertTrue(payload["closure"]["minus_divergence_split_derived"])
        self.assertTrue(payload["closure"]["feeds_plus_compatibility_equation"])
        self.assertTrue(payload["closure"]["feeds_minus_compatibility_equation"])

    def test_gradients_not_absorbed_into_k_or_qcross(self) -> None:
        closure = build_payload()["closure"]

        self.assertTrue(closure["gradients_kept_outside_K"])
        self.assertTrue(closure["gradients_kept_outside_Qcross"])
        self.assertTrue(closure["no_determinant_gradient_absorption"])

    def test_markdown_contains_product_rule_identities(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Determinant Gradient Divergence", markdown)
        self.assertIn("D_plus_nu(B_plus", markdown)
        self.assertIn("outside K and Q_cross", markdown)


if __name__ == "__main__":
    unittest.main()
