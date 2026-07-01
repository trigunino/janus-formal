from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_scalar_perturbation_system import build_payload, write_reports


class P0EFTJanusZ4ScalarPerturbationSystemScriptTests(unittest.TestCase):
    def test_scalar_scaffold_uses_rank_one_master_source(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["master_source"], "B*rho_minus + rho_plus")
        self.assertEqual(payload["zero_coupling_residual"], "0")
        self.assertTrue(payload["scalar_system_scaffold_ready"])
        self.assertFalse(payload["scalar_system_physical_ready"])
        self.assertFalse(payload["checks"]["full_boltzmann_hierarchy_derived"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_scalar_perturbation_system.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_scalar_perturbation_system.md").exists())
        self.assertIn("Psi*k**2", payload["poisson_constraint"])


if __name__ == "__main__":
    unittest.main()
