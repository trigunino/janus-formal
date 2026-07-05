import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_early_plasma_manifest import (
    Z2SigmaEarlyPlasmaComponentFunctions,
    load_active_z2sigma_early_plasma_manifest,
    write_active_z2sigma_early_plasma_manifest,
)


def _components() -> Z2SigmaEarlyPlasmaComponentFunctions:
    return Z2SigmaEarlyPlasmaComponentFunctions(
        rho_baryon_z2sigma=lambda z: (1.0 + z) ** 3,
        rho_photon_z2sigma=lambda z: 2.0 * (1.0 + z) ** 4,
        gamma_drag_z2sigma=lambda z: 100.0 + z,
    )


def _provenance() -> dict[str, str]:
    return {
        "rho_baryon_Z2Sigma": "active_baryon_density_gate",
        "rho_photon_Z2Sigma": "active_photon_density_gate",
        "Gamma_drag_Z2Sigma": "active_thomson_drag_gate",
    }


class Z2SigmaEarlyPlasmaManifestTests(unittest.TestCase):
    def test_writer_outputs_valid_active_early_plasma_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "early_plasma.json"
            write_active_z2sigma_early_plasma_manifest(
                path,
                [0.0, 10.0, 100.0],
                _components(),
                _provenance(),
            )

            payload = load_active_z2sigma_early_plasma_manifest(path)

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertIsNone(payload["z_d_bracket"])
        self.assertIn("Gamma_drag_Z2Sigma", payload["early_plasma"])
        self.assertFalse(payload["compressed_planck_lcdm_rd_used"])
        self.assertFalse(payload["observational_H0_fit_used"])

    def test_writer_rejects_forbidden_provenance_and_bad_values(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bad.json"
            bad_provenance = _provenance()
            bad_provenance["rho_photon_Z2Sigma"] = "Planck LCDM"
            with self.assertRaises(ValueError):
                write_active_z2sigma_early_plasma_manifest(
                    path,
                    [0.0, 1.0],
                    _components(),
                    bad_provenance,
                )

            bad_components = Z2SigmaEarlyPlasmaComponentFunctions(
                rho_baryon_z2sigma=lambda z: np.zeros_like(z),
                rho_photon_z2sigma=lambda z: np.ones_like(z),
                gamma_drag_z2sigma=lambda z: np.ones_like(z),
            )
            with self.assertRaises(ValueError):
                write_active_z2sigma_early_plasma_manifest(
                    path,
                    [0.0, 1.0],
                    bad_components,
                    _provenance(),
                )
            valid = Path(tmp) / "valid.json"
            write_active_z2sigma_early_plasma_manifest(
                valid,
                [0.0, 1.0],
                _components(),
                _provenance(),
            )
            text = valid.read_text(encoding="utf-8").replace(
                '"observational_H0_fit_used": false',
                '"observational_H0_fit_used": true',
            )
            valid.write_text(text, encoding="utf-8")
            with self.assertRaises(ValueError):
                load_active_z2sigma_early_plasma_manifest(valid)


if __name__ == "__main__":
    unittest.main()
