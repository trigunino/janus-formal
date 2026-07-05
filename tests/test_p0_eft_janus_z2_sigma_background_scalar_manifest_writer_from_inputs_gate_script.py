import json
import tempfile
import unittest
from pathlib import Path

from janus_lab.z2_sigma_background_manifest import load_active_z2sigma_background_scalar_manifest
from scripts.build_p0_eft_janus_z2_sigma_background_scalar_manifest_writer_from_inputs_gate import (
    build_payload,
)


def _input_payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "scalars": {
            "H0_Z2Sigma_km_s_Mpc": 70.0,
            "omega_k_Z2Sigma": 0.0,
            "gravitational_constant_si_Z2Sigma": 6.67430e-11,
        },
        "scalar_provenance": {
            "H0_Z2Sigma": "active_background_scale_gate",
            "omega_k_Z2Sigma": "active_projective_curvature_gate",
            "G_Z2Sigma": "active_low_energy_gravity_convention",
        },
    }


class P0EFTJanusZ2SigmaBackgroundScalarManifestWriterFromInputsGateTests(unittest.TestCase):
    def test_missing_input_blocks_manifest_write(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                manifest_path=Path(tmp) / "background_scalars.json",
            )

        self.assertFalse(payload["input_exists"])
        self.assertFalse(payload["manifest_written"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["primary_blocker"],
            "active_background_scalar_inputs_from_H0_Rcurv_G",
        )

    def test_valid_active_inputs_write_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "background_scalar_inputs.json"
            output_path = tmpdir / "background_scalars.json"
            input_path.write_text(json.dumps(_input_payload()), encoding="utf-8")

            payload = build_payload(input_path=input_path, manifest_path=output_path)
            manifest = load_active_z2sigma_background_scalar_manifest(output_path)

        self.assertTrue(payload["input_valid"])
        self.assertTrue(payload["manifest_written"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertIn("critical_normalization", manifest)
        self.assertFalse(manifest["compressed_planck_lcdm_background_used"])


if __name__ == "__main__":
    unittest.main()
