from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_planck_adapter_ready_closure import build_payload, write_reports


class P0EFTJanusZ4PlanckAdapterReadyClosureScriptTests(unittest.TestCase):
    def test_planck_adapter_is_ready_without_claiming_official_likelihood(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["spectrum_columns_ready"])
        self.assertTrue(payload["ell_grid_ready"])
        self.assertTrue(payload["spectra_finite"])
        self.assertTrue(payload["covariance_contract_ready"])
        self.assertTrue(payload["dry_run_chi2_finite"])
        self.assertTrue(payload["planck_likelihood_adapter_ready"])
        self.assertFalse(payload["official_planck_likelihood_executed"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_planck_adapter_ready_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_planck_adapter_ready_closure.md").exists())
        self.assertIn("official Planck", payload["scope"])


if __name__ == "__main__":
    unittest.main()
