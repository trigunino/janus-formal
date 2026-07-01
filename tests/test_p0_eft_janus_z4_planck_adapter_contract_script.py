from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_planck_adapter_contract import build_payload, write_reports


class P0EFTJanusZ4PlanckAdapterContractScriptTests(unittest.TestCase):
    def test_adapter_contract_is_declared_not_executed(self) -> None:
        payload = build_payload()
        self.assertTrue(payload["adapter_contract_ready"])
        self.assertFalse(payload["adapter_physical_ready"])
        self.assertFalse(payload["checks"]["direct_planck_likelihood_executed"])
        self.assertIn("cl_tt", payload["required_columns"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_planck_adapter_contract.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_planck_adapter_contract.md").exists())
        self.assertIn("Planck", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
