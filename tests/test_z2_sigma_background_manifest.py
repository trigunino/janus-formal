import json
import tempfile
import unittest
from pathlib import Path

from janus_lab.z2_sigma_background_manifest import (
    load_active_z2sigma_background_scalar_manifest,
    write_active_z2sigma_background_scalar_manifest,
)


def _provenance() -> dict[str, str]:
    return {
        "H0_Z2Sigma": "active_background_scale_gate",
        "omega_k_Z2Sigma": "active_projective_curvature_gate",
        "G_Z2Sigma": "active_low_energy_gravity_convention",
    }


class Z2SigmaBackgroundManifestTests(unittest.TestCase):
    def test_writer_outputs_active_background_scalar_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "background.json"
            write_active_z2sigma_background_scalar_manifest(
                path,
                h0_z2sigma_km_s_mpc=70.0,
                omega_k_z2sigma=0.01,
                gravitational_constant_si_z2sigma=1.0,
                scalar_provenance=_provenance(),
            )

            payload = load_active_z2sigma_background_scalar_manifest(path)

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["omega_k_Z2Sigma"], 0.01)
        self.assertIn("kappa_rho_crit0_Z2Sigma_SI", payload["critical_normalization"])
        self.assertFalse(payload["observational_H0_fit_used"])

    def test_writer_rejects_forbidden_provenance(self):
        for field in ["H0_Z2Sigma", "omega_k_Z2Sigma", "G_Z2Sigma"]:
            bad = _provenance()
            bad[field] = "Planck LCDM Z4"
            with self.subTest(field=field):
                with tempfile.TemporaryDirectory() as tmp:
                    with self.assertRaises(ValueError):
                        write_active_z2sigma_background_scalar_manifest(
                            Path(tmp) / "bad.json",
                            h0_z2sigma_km_s_mpc=70.0,
                            omega_k_z2sigma=0.0,
                            gravitational_constant_si_z2sigma=1.0,
                            scalar_provenance=bad,
                        )


if __name__ == "__main__":
    unittest.main()
