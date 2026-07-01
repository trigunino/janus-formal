from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_line_of_sight_integrator_target import build_payload, write_reports


class P0EFTJanusZ4LineOfSightIntegratorTargetScriptTests(unittest.TestCase):
    def test_los_integral_is_finite_with_normalized_visibility(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["source_function_declared"])
        self.assertTrue(payload["visibility_source_inserted"])
        self.assertTrue(payload["isw_source_inserted"])
        self.assertTrue(payload["finite_integral_produced"])
        self.assertLess(payload["visibility_normalization_error"], 1.0e-8)
        self.assertFalse(payload["physical_boltzmann_transfer_executed"])
        self.assertFalse(payload["planck_likelihood_adapter_ready"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_line_of_sight_integrator_target.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_line_of_sight_integrator_target.md").exists())
        self.assertIn("Planck likelihood", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
