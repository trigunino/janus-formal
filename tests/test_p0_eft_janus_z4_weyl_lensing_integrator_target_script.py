from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_weyl_lensing_integrator_target import build_payload, write_reports


class P0EFTJanusZ4WeylLensingIntegratorTargetScriptTests(unittest.TestCase):
    def test_weyl_lensing_integral_is_finite_without_planck_claim(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["weyl_potential_declared"])
        self.assertTrue(payload["lensing_kernel_declared"])
        self.assertTrue(payload["finite_kernel_integral_produced"])
        self.assertTrue(payload["projected_z4_slip_input_used"])
        self.assertTrue(payload["lensing_proxy_spectrum_exported"])
        self.assertFalse(payload["physical_planck_lensing_likelihood_executed"])
        self.assertFalse(payload["planck_likelihood_adapter_ready"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_integrator_target.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_integrator_target.md").exists())
        self.assertIn("Planck lensing likelihood", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
