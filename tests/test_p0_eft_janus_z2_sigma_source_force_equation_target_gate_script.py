from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_source_force_equation_target_gate import (
    build_payload,
    render_markdown,
)
from tests.test_z2_sigma_embedding_geometry_manifest import _manifest


class SourceForceEquationTargetGateTests(unittest.TestCase):
    def test_target_written_but_plus_minus_force_derivation_still_blocks_ready(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["target_ready"])
        self.assertFalse(payload["source_force_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["closure"]["source_route_available"])
        self.assertEqual(payload["primary_blocker"], "plus_source_force_equation_derived")
        self.assertTrue(payload["closure"]["brane_newton_second_law_bibliography_found"])
        self.assertTrue(payload["closure"]["normal_force_formula_target_refined"])
        self.assertTrue(payload["closure"]["brane_normal_force_residual_symbolic_ready"])
        self.assertFalse(payload["closure"]["brane_normal_force_residual_values_ready"])
        self.assertTrue(payload["closure"]["brane_normal_force_equation_closed_by_strict_Z2"])

    def test_embedding_manifest_moves_blocker_to_force_derivation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "embedding.json"
            path.write_text(json.dumps(_manifest()), encoding="utf-8")

            payload = build_payload(embedding_manifest_path=path)

        self.assertTrue(payload["closure"]["active_embedding_ready"])
        self.assertTrue(payload["closure"]["source_route_available"])
        self.assertEqual(payload["primary_blocker"], "plus_source_force_equation_derived")
        self.assertFalse(payload["closure"]["source_force_equations_derived"])

    def test_shortcuts_are_forbidden(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("geodesics alone", forbidden)
        self.assertIn("Lorentz admissibility", forbidden)
        self.assertIn("Q_cross", forbidden)

    def test_brane_normal_dynamics_target_is_added(self) -> None:
        payload = build_payload()

        self.assertIn("brane_normal_dynamics", payload["force_targets"])
        self.assertIn("barT", payload["force_targets"]["brane_normal_dynamics"])
        self.assertIn("battye-carter-2001", {row["id"] for row in payload["brane_bibliography"]})
        self.assertIn("carter-2000", {row["id"] for row in payload["brane_bibliography"]})
        self.assertTrue(payload["upstream"]["brane_normal_force_residual"]["symbolic_ready"])
        self.assertFalse(payload["upstream"]["brane_normal_force_residual"]["values_ready"])
        self.assertFalse(payload["source_force_ready"])

    def test_markdown_reports_next_target(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Source Force Equation Target", markdown)
        self.assertIn("Gate passed: `False`", markdown)
        self.assertIn("standard brane normal", markdown)


if __name__ == "__main__":
    unittest.main()
