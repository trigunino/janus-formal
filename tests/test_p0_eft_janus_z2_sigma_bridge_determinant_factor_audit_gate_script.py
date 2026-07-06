from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_z2_sigma_bridge_determinant_factor_audit_gate import (
    build_payload,
    render_markdown,
)


class BridgeDeterminantFactorAuditGateTests(unittest.TestCase):
    def test_determinant_audit_is_formally_closed_source_open(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["route_status"], "formal_determinant_audit_closed_source_open"
        )
        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["source_derivation_ready"])

    def test_volume_factors_are_separate_from_bridge_and_qcross(self) -> None:
        closure = build_payload()["closure"]

        self.assertTrue(closure["B_plus_declared"])
        self.assertTrue(closure["B_minus_declared"])
        self.assertTrue(closure["B_plus_B_minus_reciprocal"])
        self.assertTrue(closure["determinant_factors_kept_outside_bridge"])
        self.assertTrue(closure["Qcross_uses_same_bridge_only"])
        self.assertTrue(closure["no_Qcross_determinant_absorption"])

    def test_newtonian_limit_preserves_weakfield_signs(self) -> None:
        closure = build_payload()["closure"]

        self.assertTrue(closure["B_plus_Newtonian_limit_one"])
        self.assertTrue(closure["B_minus_Newtonian_limit_one"])
        self.assertTrue(closure["weakfield_sign_matrix_unchanged"])

    def test_markdown_reports_source_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Bridge Determinant Factor Audit", markdown)
        self.assertIn("Gate passed: `True`", markdown)
        self.assertIn("formal/source-open", markdown)


if __name__ == "__main__":
    unittest.main()
