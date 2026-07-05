import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_scale_free_omega_k_from_curvature_scale_gate import (
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


class ScaleFreeOmegaKFromCurvatureScaleGateTests(unittest.TestCase):
    def test_missing_scale_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                sign_input_path=Path(tmp) / "missing_sign.json",
                scale_input_path=Path(tmp) / "missing_scale.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["formula"].startswith("omega_k_Z2Sigma"))

    def test_valid_inputs_write_scale_free_omega_k(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            sign_path = tmpdir / "sign.json"
            scale_path = tmpdir / "scale.json"
            output_path = tmpdir / "omega.json"
            sign_path.write_text(
                json.dumps(
                    {
                        **_base(),
                        "scalars": {"k_Z2Sigma": 1},
                        "scalar_provenance": {"k_Z2Sigma": "active_topology_branch"},
                    }
                ),
                encoding="utf-8",
            )
            scale_path.write_text(
                json.dumps(
                    {
                        **_base(),
                        "scalars": {"h0_R_curv_over_c_Z2Sigma": 2.0},
                        "scalar_provenance": {
                            "h0_R_curv_over_c_Z2Sigma": "active_embedding_scale"
                        },
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                sign_input_path=sign_path,
                scale_input_path=scale_path,
                output_path=output_path,
            )
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["omega_k_value"], -0.25)
        self.assertEqual(written["scalars"]["omega_k_Z2Sigma"], -0.25)
        self.assertFalse(written["archived_z4_background_reuse_used"])

    def test_forbidden_h0_fit_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            sign_path = tmpdir / "sign.json"
            scale_path = tmpdir / "scale.json"
            sign_path.write_text(
                json.dumps(
                    {
                        **_base(),
                        "scalars": {"k_Z2Sigma": 1},
                        "scalar_provenance": {"k_Z2Sigma": "active_topology_branch"},
                    }
                ),
                encoding="utf-8",
            )
            bad = _base()
            bad["observational_H0_fit_used"] = True
            bad["scalars"] = {"h0_R_curv_over_c_Z2Sigma": 2.0}
            bad["scalar_provenance"] = {
                "h0_R_curv_over_c_Z2Sigma": "active_embedding_scale"
            }
            scale_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(
                sign_input_path=sign_path,
                scale_input_path=scale_path,
                output_path=tmpdir / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("observational_H0_fit_used", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
