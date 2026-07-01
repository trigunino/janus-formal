from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_acoustic_polarization_phase_kernel import build_payload, write_reports


class P0EFTJanusZ4AcousticPolarizationPhaseKernelTests(unittest.TestCase):
    def test_phase_kernel_is_symbolic_and_keeps_planck_false(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-acoustic-polarization-phase-kernel")
        self.assertTrue(payload["algebraic_phase_kernel_ready"])
        self.assertIn("requires_tight_coupling_quadrupole_identity", payload)
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertFalse(payload["observational_planck_gate_passed"])
        self.assertEqual(payload["formal_closure_solution"][0]["p_Q"], "1")
        self.assertEqual(payload["formal_closure_solution"][0]["p_E"], "0")
        self.assertEqual(payload["formal_closure_solution"][0]["p_Z"], "0")

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_acoustic_polarization_phase_kernel.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_acoustic_polarization_phase_kernel.md").exists())


if __name__ == "__main__":
    unittest.main()
