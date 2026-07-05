import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_background_curvature_branch_inputs_assembler_gate import (
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


class BackgroundCurvatureBranchInputsAssemblerGateTests(unittest.TestCase):
    def test_missing_inputs_block_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            payload = build_payload(
                h0_input_path=tmpdir / "h0.json",
                sign_input_path=tmpdir / "sign.json",
                radius_input_path=tmpdir / "radius.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "active_H0_and_R_curv_inputs")
        self.assertFalse(payload["input_exists"]["h0"])
        self.assertFalse(payload["input_exists"]["curvature_radius"])
        self.assertIn("h0", payload["upstream_writer_gates"])
        self.assertIn("curvature_radius", payload["upstream_writer_gates"])
        self.assertTrue(payload["nearest_background_curvature_branch_frontier"]["diagnostic_only"])

    def test_valid_inputs_write_curvature_branch_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            h0 = {
                **_base(),
                "scalars": {"H0_Z2Sigma_km_s_Mpc": 70.0},
                "scalar_provenance": {"H0_Z2Sigma": "active_background_scale_gate"},
            }
            sign = {
                **_base(),
                "scalars": {"k_Z2Sigma": 1},
                "scalar_provenance": {"k_Z2Sigma": "active_projective_topology_branch"},
                "spatial_topology": {"quotient_spatial_slice": "S3_paired_leaf_representative"},
            }
            radius = {
                **_base(),
                "scalars": {"R_curv_Z2Sigma_Mpc": 3000.0},
                "scalar_provenance": {"R_curv_Z2Sigma": "active_embedding_scale"},
            }
            h0_path = tmpdir / "h0.json"
            sign_path = tmpdir / "sign.json"
            radius_path = tmpdir / "radius.json"
            out_path = tmpdir / "branch.json"
            h0_path.write_text(json.dumps(h0), encoding="utf-8")
            sign_path.write_text(json.dumps(sign), encoding="utf-8")
            radius_path.write_text(json.dumps(radius), encoding="utf-8")

            payload = build_payload(
                h0_input_path=h0_path,
                sign_input_path=sign_path,
                radius_input_path=radius_path,
                output_path=out_path,
            )
            written = json.loads(out_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertIn("upstream_writer_gates", payload)
        self.assertEqual(written["scalars"]["k_Z2Sigma"], 1)
        self.assertEqual(written["scalars"]["R_curv_Z2Sigma_Mpc"], 3000.0)
        self.assertEqual(
            written["spatial_topology"]["quotient_spatial_slice"],
            "S3_paired_leaf_representative",
        )

    def test_forbidden_curvature_fit_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            h0 = {
                **_base(),
                "scalars": {"H0_Z2Sigma_km_s_Mpc": 70.0},
                "scalar_provenance": {"H0_Z2Sigma": "active_background_scale_gate"},
            }
            sign = {
                **_base(),
                "scalars": {"k_Z2Sigma": 1},
                "scalar_provenance": {"k_Z2Sigma": "active_projective_topology_branch"},
            }
            radius = {
                **_base(),
                "observational_curvature_fit_used": True,
                "scalars": {"R_curv_Z2Sigma_Mpc": 3000.0},
                "scalar_provenance": {"R_curv_Z2Sigma": "active_embedding_scale"},
            }
            h0_path = tmpdir / "h0.json"
            sign_path = tmpdir / "sign.json"
            radius_path = tmpdir / "radius.json"
            h0_path.write_text(json.dumps(h0), encoding="utf-8")
            sign_path.write_text(json.dumps(sign), encoding="utf-8")
            radius_path.write_text(json.dumps(radius), encoding="utf-8")

            payload = build_payload(
                h0_input_path=h0_path,
                sign_input_path=sign_path,
                radius_input_path=radius_path,
                output_path=tmpdir / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("observational_curvature_fit_used", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
