import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_active_inputs import (
    write_active_z2sigma_scale_free_background_primitive_manifest,
    write_active_z2sigma_scale_free_plasma_primitive_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_primitive_inputs_assembler_gate import (
    build_payload,
)


def _write_split_inputs(background_path: Path, plasma_path: Path) -> None:
    z = np.geomspace(1.0, 1.0e5, 128) - 1.0
    e = np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7)
    write_active_z2sigma_scale_free_background_primitive_manifest(
        background_path,
        z,
        lambda zz: np.interp(zz, z, e),
        0.0,
        float(z[-1]),
        primitive_provenance={
            "E_Z2Sigma": "active_dimensionless_background_derivation",
            "omega_k_Z2Sigma": "active_projective_curvature_derivation",
        },
    )
    write_active_z2sigma_scale_free_plasma_primitive_manifest(
        plasma_path,
        z,
        lambda zz: np.full_like(zz, 1.0 / np.sqrt(3.0)),
        lambda zz: np.interp(zz, z, e * ((z + 1.0) / 1001.0)),
        float(z[-1]),
        primitive_provenance={
            "c_s_over_c_Z2Sigma": "active_photon_baryon_sound_speed_derivation",
            "Gamma_drag_over_H0_Z2Sigma": "active_drag_over_H0_derivation",
        },
    )


class P0EFTJanusZ2SigmaBAOScaleFreePrimitiveInputsAssemblerGateTests(unittest.TestCase):
    def test_missing_split_inputs_block_assembler(self):
        payload = build_payload(Path("missing/bg.json"), Path("missing/plasma.json"), Path("missing/out.json"))

        self.assertFalse(payload["required_input_manifests_available"])
        self.assertFalse(payload["primitive_manifest_written"])
        self.assertFalse(payload["gate_passed"])

    def test_split_inputs_write_primitive_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            background_path = tmpdir / "background.json"
            plasma_path = tmpdir / "plasma.json"
            output_path = tmpdir / "primitive.json"
            _write_split_inputs(background_path, plasma_path)

            payload = build_payload(background_path, plasma_path, output_path)
            output = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["required_input_manifests_available"])
        self.assertTrue(payload["primitive_manifest_written"])
        self.assertTrue(payload["primitive_manifest_valid"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(output["manifest_kind"], "scale_free_primitive_inputs")
        self.assertIn("Gamma_drag_over_H0_Z2Sigma", output)
        self.assertEqual(
            output["primitive_provenance"]["omega_k_Z2Sigma"],
            "active_projective_curvature_derivation",
        )


if __name__ == "__main__":
    unittest.main()
