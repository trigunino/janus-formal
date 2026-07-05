import tempfile
import unittest
from pathlib import Path

import numpy as np

import scripts.build_p0_eft_janus_z2_sigma_early_plasma_density_builder_gate as gate
from janus_lab.z2_sigma_early_plasma_manifest import (
    Z2SigmaEarlyPlasmaComponentFunctions,
    write_active_z2sigma_early_plasma_manifest,
)


class P0EFTJanusZ2SigmaEarlyPlasmaDensityBuilderGateTests(unittest.TestCase):
    def test_density_builder_gate_requires_active_normalizations(self):
        payload = gate.build_payload()

        self.assertTrue(payload["baryon_density_builder_ready"])
        self.assertTrue(payload["photon_density_builder_ready"])
        self.assertTrue(payload["free_electron_density_builder_ready"])
        self.assertTrue(payload["requires_active_baryon_normalization"])
        self.assertTrue(payload["requires_active_photon_normalization"])
        self.assertTrue(payload["requires_active_ionization_fraction"])
        self.assertFalse(payload["uses_planck_lcdm_density_parameters"])
        self.assertFalse(payload["uses_planck_lcdm_recombination_history"])
        self.assertFalse(payload["uses_archived_z4_inputs"])
        self.assertFalse(payload["early_plasma_density_values_ready"])
        self.assertFalse(payload["early_plasma_manifest_status"]["valid"])

    def test_valid_early_plasma_manifest_marks_density_values_ready(self):
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
            gate.EARLY_PLASMA_MANIFEST_PATH = path
            try:
                payload = gate.build_payload()
            finally:
                gate.EARLY_PLASMA_MANIFEST_PATH = old_path

        self.assertTrue(payload["early_plasma_manifest_status"]["valid"])
        self.assertTrue(payload["early_plasma_density_values_ready"])
        self.assertTrue(payload["gate_passed"])


if __name__ == "__main__":
    unittest.main()
