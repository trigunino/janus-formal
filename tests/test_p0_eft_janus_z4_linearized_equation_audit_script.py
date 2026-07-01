from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_linearized_equation_audit import build_payload, write_reports


class P0EFTJanusZ4LinearizedEquationAuditScriptTests(unittest.TestCase):
    def test_payload_keeps_tensor_derivation_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-linearized-equation-scaffold")
        self.assertTrue(payload["z4_projection_scaffold_ready"])
        self.assertFalse(payload["full_z4_tensor_derivation_ready"])
        self.assertFalse(payload["checks"]["explicit_tensor_operator_from_action_derived"])
        self.assertTrue(payload["checks"]["independent_metric_forces_forbidden"])
        self.assertTrue(payload["checks"]["symbolic_projection_residual_zero"])
        self.assertEqual(payload["symbolic_projection"]["residual"], "Matrix([[0], [0]])")

    def test_report_writer_exports_json_and_markdown(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_linearized_equation_audit.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_linearized_equation_audit.md").exists())
        self.assertIn("Janus Z4", payload["solver_name"])


if __name__ == "__main__":
    unittest.main()
