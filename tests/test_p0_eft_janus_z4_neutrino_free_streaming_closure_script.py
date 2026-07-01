from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_neutrino_free_streaming_closure import build_payload, write_reports


class P0EFTJanusZ4NeutrinoFreeStreamingClosureScriptTests(unittest.TestCase):
    def test_free_streaming_residuals_cancel_without_physical_readiness(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["recursion_residual"], "0")
        self.assertEqual(payload["finite_tail_residual"], "0")
        self.assertTrue(payload["neutrino_free_streaming_closure_ready"])
        self.assertFalse(payload["neutrino_boltzmann_ready"])
        self.assertFalse(payload["neutrino_planck_ready"])
        self.assertFalse(payload["checks"]["physical_boltzmann_integrator_implemented"])
        self.assertFalse(payload["checks"]["planck_likelihood_ready"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_neutrino_free_streaming_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_neutrino_free_streaming_closure.md").exists())
        self.assertIn("Planck likelihood", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
