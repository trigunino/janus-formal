import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from scripts.build_p0_eft_janus_z2_sigma_direct_primitives_to_scale_free_chi2_gate import (
    build_payload,
)


def _background() -> dict:
    z = np.geomspace(1.0, 1.0e5, 128) - 1.0
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "z_grid": z.tolist(),
        "E_Z2Sigma": np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7).tolist(),
        "omega_k_Z2Sigma": 0.0,
        "z_max": float(z[-1]),
        "primitive_provenance": {
            "E_Z2Sigma": "active_dimensionless_background_derivation",
            "omega_k_Z2Sigma": "active_projective_curvature_derivation",
        },
    }


def _plasma() -> dict:
    z = np.geomspace(1.0, 1.0e5, 128) - 1.0
    e = np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "z_grid": z.tolist(),
        "c_s_over_c_Z2Sigma": np.full_like(z, 1.0 / np.sqrt(3.0)).tolist(),
        "Gamma_drag_over_H0_Z2Sigma": (e * ((z + 1.0) / 1001.0)).tolist(),
        "z_max": float(z[-1]),
        "primitive_provenance": {
            "c_s_over_c_Z2Sigma": "active_photon_baryon_sound_speed_derivation",
            "Gamma_drag_over_H0_Z2Sigma": "active_drag_over_H0_derivation",
        },
    }


class DirectPrimitivesToScaleFreeChi2GateTests(unittest.TestCase):
    def test_missing_direct_inputs_block_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            payload = build_payload(
                background_normalization_path=tmpdir / "missing_background.json",
                plasma_normalization_path=tmpdir / "missing_plasma.json",
                background_primitive_path=tmpdir / "background.json",
                plasma_primitive_path=tmpdir / "plasma.json",
                primitive_input_path=tmpdir / "primitive.json",
                scale_free_input_path=tmpdir / "bao.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["background_writer_passed"])
        self.assertFalse(payload["plasma_writer_passed"])

    def test_direct_inputs_evaluate_bao_chi2(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            background_path = tmpdir / "background_norm.json"
            plasma_path = tmpdir / "plasma_norm.json"
            background_path.write_text(json.dumps(_background()), encoding="utf-8")
            plasma_path.write_text(json.dumps(_plasma()), encoding="utf-8")

            payload = build_payload(
                background_normalization_path=background_path,
                plasma_normalization_path=plasma_path,
                background_primitive_path=tmpdir / "background.json",
                plasma_primitive_path=tmpdir / "plasma.json",
                primitive_input_path=tmpdir / "primitive.json",
                scale_free_input_path=tmpdir / "bao.json",
            )

        self.assertTrue(payload["background_writer_passed"])
        self.assertTrue(payload["plasma_writer_passed"])
        self.assertTrue(payload["primitive_inputs_assembler_passed"])
        self.assertTrue(payload["bao_chi2_evaluated"])
        self.assertIsNotNone(payload["chi2_DESI_DR2_BAO"])
        self.assertTrue(payload["Gamma_drag_over_H0_Z2Sigma_available"])
        self.assertFalse(payload["uses_observational_H0_fit"])


if __name__ == "__main__":
    unittest.main()
