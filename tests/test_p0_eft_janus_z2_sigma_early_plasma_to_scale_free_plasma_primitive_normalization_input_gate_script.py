import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_early_plasma_manifest import (
    Z2SigmaEarlyPlasmaComponentFunctions,
    write_active_z2sigma_early_plasma_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_to_scale_free_plasma_primitive_normalization_input_gate import (
    build_payload,
)


def _write_early(path: Path) -> None:
    z = np.geomspace(1.0, 1.0e4, 64) - 1.0
    write_active_z2sigma_early_plasma_manifest(
        path,
        z,
        Z2SigmaEarlyPlasmaComponentFunctions(
            rho_baryon_z2sigma=lambda zz: 0.05 * (1.0 + zz) ** 3,
            rho_photon_z2sigma=lambda zz: 5.0e-5 * (1.0 + zz) ** 4,
            gamma_drag_z2sigma=lambda zz: 70.0 * (1.0 + zz / 1000.0),
        ),
        {
            "rho_baryon_Z2Sigma": "active_baryon_density_gate",
            "rho_photon_Z2Sigma": "active_photon_density_gate",
            "Gamma_drag_Z2Sigma": "active_thomson_drag_gate",
        },
        z_d_bracket=(100.0, 2000.0),
    )


def _write_h0(path: Path) -> None:
    path.write_text(
        json.dumps(
            {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_background_reuse_used": False,
                "observational_H0_fit_used": False,
                "scalars": {"H0_Z2Sigma_km_s_Mpc": 70.0},
                "scalar_provenance": {"H0_Z2Sigma": "active_background_scale_gate"},
            },
            indent=2,
        ),
        encoding="utf-8",
    )


class EarlyPlasmaToScaleFreePlasmaPrimitiveNormalizationInputGateTests(unittest.TestCase):
    def test_missing_inputs_block_gate(self):
        payload = build_payload(
            early_plasma_path=Path("missing_early.json"),
            h0_path=Path("missing_h0.json"),
            normalization_path=Path("missing_norm.json"),
            plasma_primitive_path=Path("missing_plasma.json"),
        )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["normalization_manifest_written"])
        self.assertFalse(payload["uses_observational_H0_fit"])

    def test_early_plasma_and_h0_write_normalization_and_plasma_primitive(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            early = root / "early.json"
            h0 = root / "h0.json"
            norm = root / "plasma_norm.json"
            plasma = root / "plasma_primitive.json"
            _write_early(early)
            _write_h0(h0)

            payload = build_payload(
                early_plasma_path=early,
                h0_path=h0,
                normalization_path=norm,
                plasma_primitive_path=plasma,
            )
            norm_payload = json.loads(norm.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["downstream_plasma_writer_passed"])
        self.assertEqual(norm_payload["source"], "active_derived")
        self.assertIn("Gamma_drag_over_H0_Z2Sigma", norm_payload)
        self.assertFalse(norm_payload["observational_H0_fit_used"])


if __name__ == "__main__":
    unittest.main()
