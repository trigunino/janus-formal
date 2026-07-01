from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_parity_polarization_mixer import build_payload, write_reports


class P0EFTJanusZ4ParityPolarizationMixerTests(unittest.TestCase):
    def test_mixer_is_branch_only_and_reports_viability(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-parity-polarization-mixer")
        self.assertTrue(payload["branch_only_diagnostic"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertFalse(payload["observational_planck_gate_passed"])
        self.assertIsInstance(payload["safe_solver_integration_recommended"], bool)
        self.assertGreater(len(payload["candidates"]), 0)
        self.assertIn("score", payload["best_candidate"])
        self.assertIn("te_restored", payload["best_candidate"]["score"])
        self.assertIn("ee_norm_preserved", payload["best_candidate"]["score"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_parity_polarization_mixer.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_parity_polarization_mixer.md").exists())


if __name__ == "__main__":
    unittest.main()
