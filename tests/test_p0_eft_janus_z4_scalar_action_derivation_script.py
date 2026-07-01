from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_scalar_action_derivation import build_payload, write_reports


class P0EFTJanusZ4ScalarActionDerivationScriptTests(unittest.TestCase):
    def test_scalar_coefficients_are_action_normalized(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["poisson_coefficient"], "4*pi*G")
        self.assertEqual(payload["momentum_coefficient"], "4*pi*G")
        self.assertEqual(payload["slip_coefficient"], "12*pi*G")
        self.assertEqual(payload["poisson_residual"], "0")
        self.assertEqual(payload["momentum_residual"], "0")
        self.assertEqual(payload["slip_residual"], "0")
        self.assertTrue(payload["scalar_action_derived_ready"])
        self.assertTrue(payload["full_z4_scalar_perturbations_derived"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_scalar_action_derivation.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_scalar_action_derivation.md").exists())
        self.assertIn("photon-baryon", payload["scope"])


if __name__ == "__main__":
    unittest.main()
