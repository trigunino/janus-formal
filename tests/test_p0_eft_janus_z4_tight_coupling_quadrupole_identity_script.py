from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_tight_coupling_quadrupole_identity import build_payload, write_reports


class P0EFTJanusZ4TightCouplingQuadrupoleIdentityTests(unittest.TestCase):
    def test_identity_is_derived_without_solver_or_planck_claim(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-tight-coupling-quadrupole-identity")
        self.assertTrue(payload["tight_coupling_limit_declared"])
        self.assertTrue(payload["leakage_free"])
        self.assertTrue(payload["tight_coupling_quadrupole_identity_derived"])
        self.assertTrue(payload["feeds_phase_kernel"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertEqual(payload["identity_residual_after_substitution"], "0")
        self.assertEqual(payload["phase_kernel_residual_after_identity"], "0")

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_tight_coupling_quadrupole_identity.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_tight_coupling_quadrupole_identity.md").exists())


if __name__ == "__main__":
    unittest.main()
