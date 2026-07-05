import tempfile
import unittest
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_active_inputs import (
    write_active_z2sigma_scale_free_background_primitive_manifest,
    write_active_z2sigma_scale_free_plasma_primitive_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_split_primitives_to_scale_free_chi2_gate import (
    build_payload,
)


def _write_split_inputs(background_path: Path, plasma_path: Path) -> None:
    z = np.geomspace(1.0, 1.0e5, 256) - 1.0
    e = np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7)
    gamma_over_h0 = e * ((z + 1.0) / 1001.0)
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
        lambda zz: np.interp(zz, z, gamma_over_h0),
        float(z[-1]),
        primitive_provenance={
            "c_s_over_c_Z2Sigma": "active_photon_baryon_sound_speed_derivation",
            "Gamma_drag_over_H0_Z2Sigma": "active_drag_over_H0_derivation",
        },
    )


class P0EFTJanusZ2SigmaBAOSplitPrimitivesToScaleFreeChi2GateTests(unittest.TestCase):
    def test_missing_split_inputs_block_gate(self):
        payload = build_payload(
            Path("missing/background.json"),
            Path("missing/plasma.json"),
            Path("missing/primitive.json"),
            Path("missing/scale_free.json"),
        )

        self.assertFalse(payload["primitive_inputs_assembler_passed"])
        self.assertFalse(payload["bao_chi2_evaluated"])
        self.assertFalse(payload["gate_passed"])

    def test_split_inputs_run_to_scale_free_chi2(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            background = tmpdir / "background.json"
            plasma = tmpdir / "plasma.json"
            primitive = tmpdir / "primitive.json"
            scale_free = tmpdir / "scale_free.json"
            _write_split_inputs(background, plasma)

            payload = build_payload(background, plasma, primitive, scale_free)

        self.assertTrue(payload["primitive_inputs_assembler_passed"])
        self.assertTrue(payload["primitive_chi2_passed"])
        self.assertTrue(payload["bao_chi2_evaluated"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(len(payload["prediction_vector"]), 13)
        self.assertEqual(len(payload["residual_vector"]), 13)
        self.assertGreater(payload["chi2_DESI_DR2_BAO"], 0.0)
        self.assertFalse(payload["uses_compressed_planck_lcdm"])
        self.assertFalse(payload["uses_archived_z4"])
        self.assertFalse(payload["uses_observational_H0_fit"])


if __name__ == "__main__":
    unittest.main()
