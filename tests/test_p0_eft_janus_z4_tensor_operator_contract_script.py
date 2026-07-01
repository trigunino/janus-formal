from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_tensor_operator_contract import build_payload, write_reports


class P0EFTJanusZ4TensorOperatorContractScriptTests(unittest.TestCase):
    def test_rank_one_master_source_is_derived_from_coupled_equations(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-tensor-operator-contract")
        self.assertEqual(payload["mixing_determinant"], "0")
        self.assertEqual(payload["residual"], "Matrix([[0], [0]])")
        self.assertTrue(payload["tensor_operator_from_coupled_equations_ready"])
        self.assertFalse(payload["full_action_tensor_derivation_ready"])
        self.assertFalse(payload["checks"]["action_variation_from_janus_action_derived"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_tensor_operator_contract.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_tensor_operator_contract.md").exists())
        self.assertIn("T_plus", payload["master_source"])


if __name__ == "__main__":
    unittest.main()
