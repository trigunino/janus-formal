import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_background_scalar_inputs_assembler_gate import (
    build_payload,
)


def _scalar_payload(field: str, provenance_key: str, value: float, provenance: str) -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "scalars": {field: value},
        "scalar_provenance": {provenance_key: provenance},
    }


class P0EFTJanusZ2SigmaBackgroundScalarInputsAssemblerGateTests(unittest.TestCase):
    def test_missing_scalar_inputs_block_assembler(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                h0_path=Path(tmp) / "h0.json",
                curvature_path=Path(tmp) / "curvature.json",
                gravity_path=Path(tmp) / "gravity.json",
                output_path=Path(tmp) / "background_scalar_inputs.json",
            )
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["background_scalar_inputs_written"])
        self.assertEqual(
            payload["primary_blocker"],
            "active_H0_and_R_curv_dimensionful_normalization",
        )

    def test_valid_scalar_inputs_write_background_scalar_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            h0 = tmpdir / "h0.json"
            curvature = tmpdir / "curvature.json"
            gravity = tmpdir / "gravity.json"
            output = tmpdir / "background_scalar_inputs.json"
            h0.write_text(
                json.dumps(
                    _scalar_payload(
                        "H0_Z2Sigma_km_s_Mpc", "H0_Z2Sigma", 70.0, "active_background_scale"
                    )
                ),
                encoding="utf-8",
            )
            curvature.write_text(
                json.dumps(
                    _scalar_payload(
                        "omega_k_Z2Sigma", "omega_k_Z2Sigma", 0.0, "active_projective_curvature"
                    )
                ),
                encoding="utf-8",
            )
            gravity.write_text(
                json.dumps(
                    _scalar_payload(
                        "gravitational_constant_si_Z2Sigma",
                        "G_Z2Sigma",
                        6.67430e-11,
                        "active_low_energy_gravity_convention",
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                h0_path=h0,
                curvature_path=curvature,
                gravity_path=gravity,
                output_path=output,
            )
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(written["scalars"]["omega_k_Z2Sigma"], 0.0)
        self.assertFalse(written["observational_H0_fit_used"])

    def test_forbidden_h0_provenance_blocks_assembler(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            h0 = tmpdir / "h0.json"
            curvature = tmpdir / "curvature.json"
            gravity = tmpdir / "gravity.json"
            output = tmpdir / "background_scalar_inputs.json"
            h0.write_text(
                json.dumps(
                    _scalar_payload("H0_Z2Sigma_km_s_Mpc", "H0_Z2Sigma", 70.0, "Planck H0")
                ),
                encoding="utf-8",
            )
            curvature.write_text(
                json.dumps(
                    _scalar_payload(
                        "omega_k_Z2Sigma", "omega_k_Z2Sigma", 0.0, "active_projective_curvature"
                    )
                ),
                encoding="utf-8",
            )
            gravity.write_text(
                json.dumps(
                    _scalar_payload(
                        "gravitational_constant_si_Z2Sigma",
                        "G_Z2Sigma",
                        6.67430e-11,
                        "active_low_energy_gravity_convention",
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                h0_path=h0,
                curvature_path=curvature,
                gravity_path=gravity,
                output_path=output,
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
