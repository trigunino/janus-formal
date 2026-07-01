from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_tt_swisw_derivation import build_payload, write_reports


class P0EFTJanusZ4TTSWISWDerivationTests(unittest.TestCase):
    def test_derivation_closes_symbolic_residuals_without_solver_change(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-tt-swisw-derivation")
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertTrue(payload["tt_acoustic_derivation"]["derived"])
        self.assertTrue(payload["swisw_regularization"]["derived"])
        self.assertEqual(payload["swisw_regularization"]["isw_regularization_residual"], "0")
        self.assertEqual(payload["swisw_regularization"]["sw_regularization_residual"], "0")
        self.assertTrue(payload["implementation_guard"]["do_not_add_new_primordial_shape_kernel"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_tt_swisw_derivation.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_tt_swisw_derivation.md").exists())


if __name__ == "__main__":
    unittest.main()
