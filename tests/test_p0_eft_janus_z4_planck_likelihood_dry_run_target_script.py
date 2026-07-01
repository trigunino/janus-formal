from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_planck_likelihood_dry_run_target import build_payload, write_reports


class P0EFTJanusZ4PlanckLikelihoodDryRunTargetScriptTests(unittest.TestCase):
    def test_dry_run_likelihood_produces_finite_chi2_without_official_planck(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["residual_vector_declared"])
        self.assertTrue(payload["covariance_diagonal_positive"])
        self.assertTrue(payload["finite_chi2_produced"])
        self.assertTrue(payload["spectra_adapter_input_used"])
        self.assertGreater(payload["dof"], 0)
        self.assertFalse(payload["official_planck_likelihood_executed"])
        self.assertFalse(payload["planck_likelihood_adapter_ready"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_planck_likelihood_dry_run_target.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_planck_likelihood_dry_run_target.md").exists())
        self.assertIn("official Planck", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
