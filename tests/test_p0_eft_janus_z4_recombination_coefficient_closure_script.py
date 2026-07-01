from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_recombination_coefficient_closure import build_payload, write_reports


class P0EFTJanusZ4RecombinationCoefficientClosureScriptTests(unittest.TestCase):
    def test_detailed_balance_closes_peebles_equilibrium(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["peebles_equilibrium_residual"], "0")
        self.assertTrue(payload["saha_equilibrium_declared"])
        self.assertTrue(payload["detailed_balance_relation_declared"])
        self.assertTrue(payload["peebles_equilibrium_residual_closed"])
        self.assertTrue(payload["coefficients_positive"])
        self.assertFalse(payload["coefficients_calibrated_from_microphysics"])
        self.assertFalse(payload["physical_recombination_visibility_nonproxy"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_recombination_coefficient_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_recombination_coefficient_closure.md").exists())
        self.assertIn("Z4 microphysics", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
