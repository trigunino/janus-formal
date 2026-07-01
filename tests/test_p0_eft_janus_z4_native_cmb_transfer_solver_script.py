from __future__ import annotations

import csv
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import SPECTRA_PATH, build_payload, write_reports


class P0EFTJanusZ4NativeCMBTransferSolverScriptTests(unittest.TestCase):
    def test_native_transfer_solver_exports_finite_spectra(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["native_transfer_solver_ready"])
        self.assertTrue(payload["spherical_bessel_projection_used"])
        self.assertTrue(payload["dense_lensing_ell_grid_used"])
        self.assertTrue(payload["visibility_weighted_sources_used"])
        self.assertTrue(payload["coupled_photon_baryon_sources_used"])
        self.assertTrue(payload["dedicated_weyl_lensing_source_used"])
        self.assertTrue(payload["cmb_lensing_phi_kernel_used"])
        self.assertTrue(payload["pp_median_calibration_target_used"])
        self.assertTrue(payload["tight_coupling_polarization_source_used"])
        self.assertTrue(payload["spin2_e_mode_projection_used"])
        self.assertTrue(payload["primordial_power_integrated"])
        self.assertTrue(payload["no_legacy_camb_fork_required"])
        self.assertFalse(payload["official_planck_likelihood_executed"])
        self.assertTrue(SPECTRA_PATH.exists())
        with SPECTRA_PATH.open(encoding="utf-8") as handle:
            rows = list(csv.DictReader(handle))
        self.assertEqual(len(rows), payload["row_count"])
        self.assertIn("cl_tt", rows[0])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_native_cmb_transfer_solver.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_native_cmb_transfer_solver.md").exists())
        self.assertGreaterEqual(payload["ell_max"], 1000)


if __name__ == "__main__":
    unittest.main()
