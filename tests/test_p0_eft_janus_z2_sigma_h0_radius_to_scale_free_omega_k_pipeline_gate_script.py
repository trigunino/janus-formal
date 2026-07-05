import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_h0_radius_to_scale_free_omega_k_pipeline_gate import (
    build_payload,
)


def _base() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
    }


class H0RadiusToScaleFreeOmegaKPipelineGateTests(unittest.TestCase):
    def test_missing_inputs_block_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                h0_input_path=root / "missing_h0.json",
                radius_input_path=root / "missing_radius.json",
                sign_input_path=root / "missing_sign.json",
                scale_normalization_path=root / "scale_norm.json",
                scale_input_path=root / "scale.json",
                omega_k_output_path=root / "omega.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["uses_observational_H0_fit"])

    def test_active_h0_radius_and_sign_write_scale_free_omega_k(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            h0 = root / "h0.json"
            radius = root / "radius.json"
            sign = root / "sign.json"
            scale_norm = root / "scale_norm.json"
            scale = root / "scale.json"
            omega = root / "omega.json"
            h0.write_text(
                json.dumps({
                    **_base(),
                    "scalars": {"H0_Z2Sigma_km_s_Mpc": 70.0},
                    "scalar_provenance": {"H0_Z2Sigma": "active_background_scale_gate"},
                }),
                encoding="utf-8",
            )
            radius.write_text(
                json.dumps({
                    **_base(),
                    "scalars": {"R_curv_Z2Sigma_Mpc": 3000.0},
                    "scalar_provenance": {"R_curv_Z2Sigma": "active_embedding_scale"},
                }),
                encoding="utf-8",
            )
            sign.write_text(
                json.dumps({
                    **_base(),
                    "scalars": {"k_Z2Sigma": 1},
                    "scalar_provenance": {"k_Z2Sigma": "active_projective_spatial_branch"},
                }),
                encoding="utf-8",
            )

            payload = build_payload(
                h0_input_path=h0,
                radius_input_path=radius,
                sign_input_path=sign,
                scale_normalization_path=scale_norm,
                scale_input_path=scale,
                omega_k_output_path=omega,
            )
            written = json.loads(omega.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["scale_free_omega_k_passed"])
        self.assertIn("omega_k_Z2Sigma", written["scalars"])
        self.assertFalse(written["archived_z4_background_reuse_used"])


if __name__ == "__main__":
    unittest.main()
