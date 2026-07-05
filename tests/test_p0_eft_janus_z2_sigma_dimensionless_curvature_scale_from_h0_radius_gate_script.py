import json
import tempfile
import unittest
from pathlib import Path

from janus_lab.constants import SPEED_OF_LIGHT_KM_S
from scripts.build_p0_eft_janus_z2_sigma_dimensionless_curvature_scale_from_h0_radius_gate import (
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


class DimensionlessCurvatureScaleFromH0RadiusGateTests(unittest.TestCase):
    def test_missing_inputs_block_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            payload = build_payload(
                h0_input_path=tmpdir / "missing_h0.json",
                radius_input_path=tmpdir / "missing_radius.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["input_exists"]["h0"])
        self.assertFalse(payload["input_exists"]["curvature_radius"])

    def test_valid_inputs_write_dimensionless_scale_normalization(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            h0 = {
                **_base(),
                "scalars": {"H0_Z2Sigma_km_s_Mpc": 70.0},
                "scalar_provenance": {"H0_Z2Sigma": "active_background_scale_gate"},
            }
            radius = {
                **_base(),
                "scalars": {"R_curv_Z2Sigma_Mpc": 3000.0},
                "scalar_provenance": {"R_curv_Z2Sigma": "active_embedding_scale"},
            }
            h0_path = tmpdir / "h0.json"
            radius_path = tmpdir / "radius.json"
            output_path = tmpdir / "scale.json"
            h0_path.write_text(json.dumps(h0), encoding="utf-8")
            radius_path.write_text(json.dumps(radius), encoding="utf-8")

            payload = build_payload(
                h0_input_path=h0_path,
                radius_input_path=radius_path,
                output_path=output_path,
            )
            output = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        expected = 70.0 * 3000.0 / SPEED_OF_LIGHT_KM_S
        self.assertAlmostEqual(payload["h0_R_curv_over_c_value"], expected)
        self.assertAlmostEqual(
            output["scalars"]["h0_R_curv_over_c_Z2Sigma"],
            expected,
        )
        self.assertFalse(output["observational_H0_fit_used"])
        self.assertFalse(output["observational_curvature_fit_used"])

    def test_forbidden_provenance_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            h0 = {
                **_base(),
                "scalars": {"H0_Z2Sigma_km_s_Mpc": 70.0},
                "scalar_provenance": {"H0_Z2Sigma": "Planck LCDM"},
            }
            radius = {
                **_base(),
                "scalars": {"R_curv_Z2Sigma_Mpc": 3000.0},
                "scalar_provenance": {"R_curv_Z2Sigma": "active_embedding_scale"},
            }
            h0_path = tmpdir / "h0.json"
            radius_path = tmpdir / "radius.json"
            h0_path.write_text(json.dumps(h0), encoding="utf-8")
            radius_path.write_text(json.dumps(radius), encoding="utf-8")

            payload = build_payload(
                h0_input_path=h0_path,
                radius_input_path=radius_path,
                output_path=tmpdir / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
