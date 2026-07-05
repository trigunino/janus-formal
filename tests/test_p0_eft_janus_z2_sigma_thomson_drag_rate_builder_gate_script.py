import tempfile
import unittest
from pathlib import Path

import numpy as np
import json

import scripts.build_p0_eft_janus_z2_sigma_thomson_drag_rate_builder_gate as gate
from janus_lab.z2_sigma_early_plasma_manifest import (
    Z2SigmaEarlyPlasmaComponentFunctions,
    write_active_z2sigma_early_plasma_manifest,
)
from janus_lab.z2_sigma_background_manifest import write_active_z2sigma_background_scalar_manifest


class P0EFTJanusZ2SigmaThomsonDragRateBuilderGateTests(unittest.TestCase):
    def test_drag_rate_builder_declares_active_inputs_only(self):
        payload = gate.build_payload()

        self.assertTrue(payload["thomson_drag_rate_builder_ready"])
        self.assertTrue(payload["Gamma_drag_over_H0_builder_ready"])
        self.assertTrue(payload["requires_active_free_electron_density"])
        self.assertTrue(payload["requires_active_baryon_density"])
        self.assertTrue(payload["requires_active_photon_density"])
        self.assertTrue(payload["requires_active_H0_Z2Sigma"])
        self.assertFalse(payload["uses_planck_lcdm_recombination_history"])
        self.assertFalse(payload["uses_archived_z4_inputs"])
        self.assertFalse(payload["Gamma_drag_values_ready"])
        self.assertFalse(payload["Gamma_drag_over_H0_values_ready"])
        self.assertFalse(payload["early_plasma_manifest_status"]["valid"])
        self.assertFalse(payload["background_scalar_manifest_status"]["valid"])
        self.assertFalse(payload["background_h0_input_status"]["valid"])

    def test_valid_early_plasma_manifest_marks_gamma_values_ready_but_not_gamma_over_h0(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "early_plasma.json"
            z = np.asarray([0.0, 10.0])
            write_active_z2sigma_early_plasma_manifest(
                path,
                z,
                Z2SigmaEarlyPlasmaComponentFunctions(
                    rho_baryon_z2sigma=lambda zz: np.ones_like(zz) + zz,
                    rho_photon_z2sigma=lambda zz: np.ones_like(zz) + 2.0 * zz,
                    gamma_drag_z2sigma=lambda zz: np.ones_like(zz) + 3.0 * zz,
                ),
                {
                    "rho_baryon_Z2Sigma": "active_baryon_density",
                    "rho_photon_Z2Sigma": "active_photon_density",
                    "Gamma_drag_Z2Sigma": "active_drag_rate",
                },
            )
            old_path = gate.EARLY_PLASMA_MANIFEST_PATH
            old_h0 = gate.BACKGROUND_H0_INPUT_PATH
            gate.EARLY_PLASMA_MANIFEST_PATH = path
            gate.BACKGROUND_H0_INPUT_PATH = Path(tmp) / "missing_h0.json"
            try:
                payload = gate.build_payload()
            finally:
                gate.EARLY_PLASMA_MANIFEST_PATH = old_path
                gate.BACKGROUND_H0_INPUT_PATH = old_h0

        self.assertTrue(payload["early_plasma_manifest_status"]["valid"])
        self.assertTrue(payload["Gamma_drag_values_ready"])
        self.assertFalse(payload["Gamma_drag_over_H0_values_ready"])
        self.assertFalse(payload["gate_passed"])

    def test_valid_early_plasma_and_h0_input_mark_scale_free_gamma_over_h0_ready(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            early_path = tmpdir / "early_plasma.json"
            h0_path = tmpdir / "h0.json"
            z = np.asarray([0.0, 10.0])
            write_active_z2sigma_early_plasma_manifest(
                early_path,
                z,
                Z2SigmaEarlyPlasmaComponentFunctions(
                    rho_baryon_z2sigma=lambda zz: np.ones_like(zz) + zz,
                    rho_photon_z2sigma=lambda zz: np.ones_like(zz) + 2.0 * zz,
                    gamma_drag_z2sigma=lambda zz: np.ones_like(zz) + 3.0 * zz,
                ),
                {
                    "rho_baryon_Z2Sigma": "active_baryon_density",
                    "rho_photon_Z2Sigma": "active_photon_density",
                    "Gamma_drag_Z2Sigma": "active_drag_rate",
                },
            )
            h0_path.write_text(
                json.dumps({
                    "active_core": "Z2_tunnel_Sigma",
                    "source": "active_derived",
                    "compressed_planck_lcdm_background_used": False,
                    "archived_z4_background_reuse_used": False,
                    "observational_H0_fit_used": False,
                    "observational_curvature_fit_used": False,
                    "scalars": {"H0_Z2Sigma_km_s_Mpc": 70.0},
                    "scalar_provenance": {"H0_Z2Sigma": "active_background_scale"},
                }),
                encoding="utf-8",
            )
            old_early = gate.EARLY_PLASMA_MANIFEST_PATH
            old_h0 = gate.BACKGROUND_H0_INPUT_PATH
            old_background = gate.BACKGROUND_SCALAR_MANIFEST_PATH
            gate.EARLY_PLASMA_MANIFEST_PATH = early_path
            gate.BACKGROUND_H0_INPUT_PATH = h0_path
            gate.BACKGROUND_SCALAR_MANIFEST_PATH = tmpdir / "missing_background.json"
            try:
                payload = gate.build_payload()
            finally:
                gate.EARLY_PLASMA_MANIFEST_PATH = old_early
                gate.BACKGROUND_H0_INPUT_PATH = old_h0
                gate.BACKGROUND_SCALAR_MANIFEST_PATH = old_background

        self.assertTrue(payload["early_plasma_manifest_status"]["valid"])
        self.assertFalse(payload["background_scalar_manifest_status"]["valid"])
        self.assertTrue(payload["background_h0_input_status"]["valid"])
        self.assertTrue(payload["Gamma_drag_over_H0_values_ready"])
        self.assertTrue(payload["scale_free_Gamma_drag_over_H0_from_active_H0_ready"])
        self.assertTrue(payload["gate_passed"])

    def test_valid_early_plasma_and_background_manifests_mark_gamma_over_h0_ready(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            early_path = tmpdir / "early_plasma.json"
            background_path = tmpdir / "background_scalars.json"
            z = np.asarray([0.0, 10.0])
            write_active_z2sigma_early_plasma_manifest(
                early_path,
                z,
                Z2SigmaEarlyPlasmaComponentFunctions(
                    rho_baryon_z2sigma=lambda zz: np.ones_like(zz) + zz,
                    rho_photon_z2sigma=lambda zz: np.ones_like(zz) + 2.0 * zz,
                    gamma_drag_z2sigma=lambda zz: np.ones_like(zz) + 3.0 * zz,
                ),
                {
                    "rho_baryon_Z2Sigma": "active_baryon_density",
                    "rho_photon_Z2Sigma": "active_photon_density",
                    "Gamma_drag_Z2Sigma": "active_drag_rate",
                },
            )
            write_active_z2sigma_background_scalar_manifest(
                background_path,
                h0_z2sigma_km_s_mpc=70.0,
                omega_k_z2sigma=0.0,
                gravitational_constant_si_z2sigma=6.67430e-11,
                scalar_provenance={
                    "H0_Z2Sigma": "active_background_scale",
                    "omega_k_Z2Sigma": "active_projective_curvature",
                    "G_Z2Sigma": "active_low_energy_gravity_convention",
                },
            )
            old_early = gate.EARLY_PLASMA_MANIFEST_PATH
            old_background = gate.BACKGROUND_SCALAR_MANIFEST_PATH
            old_h0 = gate.BACKGROUND_H0_INPUT_PATH
            gate.EARLY_PLASMA_MANIFEST_PATH = early_path
            gate.BACKGROUND_SCALAR_MANIFEST_PATH = background_path
            gate.BACKGROUND_H0_INPUT_PATH = tmpdir / "missing_h0.json"
            try:
                payload = gate.build_payload()
            finally:
                gate.EARLY_PLASMA_MANIFEST_PATH = old_early
                gate.BACKGROUND_SCALAR_MANIFEST_PATH = old_background
                gate.BACKGROUND_H0_INPUT_PATH = old_h0

        self.assertTrue(payload["early_plasma_manifest_status"]["valid"])
        self.assertTrue(payload["background_scalar_manifest_status"]["valid"])
        self.assertTrue(payload["Gamma_drag_values_ready"])
        self.assertTrue(payload["Gamma_drag_over_H0_values_ready"])
        self.assertTrue(payload["gate_passed"])


if __name__ == "__main__":
    unittest.main()
