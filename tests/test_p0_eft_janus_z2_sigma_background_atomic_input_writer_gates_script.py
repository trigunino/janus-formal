import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_background_curvature_input_writer_gate import (
    build_payload as build_curvature,
)
from scripts.build_p0_eft_janus_z2_sigma_background_gravity_input_writer_gate import (
    build_payload as build_gravity,
)
from scripts.build_p0_eft_janus_z2_sigma_background_h0_input_writer_gate import (
    build_payload as build_h0,
)


def _payload(field: str, key: str, value: float, provenance: str = "active source") -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "scalars": {field: value},
        "scalar_provenance": {key: provenance},
    }


class P0EFTJanusZ2SigmaBackgroundAtomicInputWriterGateTests(unittest.TestCase):
    def test_missing_inputs_block_writers(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            h0_payload = build_h0(input_path=tmpdir / "missing.json")
            self.assertFalse(h0_payload["gate_passed"])
            self.assertEqual(h0_payload["primary_blocker"], "active_H0_scale_normalization_from_RSigma")
            self.assertEqual(h0_payload["missing_active_artifact"], str(tmpdir / "missing.json"))
            self.assertTrue(h0_payload["requires_active_H0_scale_normalization"])
            self.assertTrue(h0_payload["dimensionless_H0R_over_c_insufficient_for_H0"])
            self.assertEqual(
                h0_payload["normalization_source_frontier"]["source_gate"],
                "P0EFTJanusZ2SigmaRSigmaSolutionToEmbeddingCurvatureBranchGate",
            )
            self.assertIn(
                "counterterm_radial_block",
                h0_payload["normalization_source_frontier"]["blocks"],
            )
            curvature_payload = build_curvature(input_path=tmpdir / "missing.json")
            self.assertFalse(curvature_payload["gate_passed"])
            self.assertTrue(curvature_payload["projective_tunnel_two_fold_topology_ready"])
            self.assertFalse(curvature_payload["topology_alone_fixes_numeric_omega_k"])
            self.assertFalse(curvature_payload["active_FLRW_spatial_metric_branch_gate_passed"])
            self.assertFalse(curvature_payload["active_FLRW_spatial_metric_branch_values_ready"])
            self.assertFalse(curvature_payload["curvature_normalization_from_branch_gate_passed"])
            self.assertTrue(curvature_payload["computes_omega_k_from_k_Rcurv_H0"])
            self.assertTrue(
                curvature_payload["requires_active_FLRW_curvature_radius_or_embedding_scale"]
            )
            self.assertFalse(build_gravity(input_path=tmpdir / "missing.json")["gate_passed"])

    def test_valid_inputs_write_atomic_payloads(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            h0 = tmpdir / "h0.json"
            curvature = tmpdir / "curv.json"
            gravity = tmpdir / "g.json"
            h0.write_text(
                json.dumps(_payload("H0_Z2Sigma_km_s_Mpc", "H0_Z2Sigma", 70.0)),
                encoding="utf-8",
            )
            curvature.write_text(
                json.dumps(_payload("omega_k_Z2Sigma", "omega_k_Z2Sigma", 0.0)),
                encoding="utf-8",
            )
            gravity.write_text(
                json.dumps(
                    _payload("gravitational_constant_si_Z2Sigma", "G_Z2Sigma", 6.67430e-11)
                ),
                encoding="utf-8",
            )
            out_h0 = tmpdir / "out_h0.json"
            out_curv = tmpdir / "out_curv.json"
            out_g = tmpdir / "out_g.json"

            h0_written = build_h0(input_path=h0, output_path=out_h0)
            self.assertTrue(h0_written["gate_passed"])
            self.assertEqual(h0_written["primary_blocker"], "none")
            self.assertTrue(
                build_curvature(input_path=curvature, output_path=out_curv)["gate_passed"]
            )
            self.assertTrue(build_gravity(input_path=gravity, output_path=out_g)["gate_passed"])

            self.assertIn("H0_Z2Sigma_km_s_Mpc", json.loads(out_h0.read_text())["scalars"])
            self.assertIn("omega_k_Z2Sigma", json.loads(out_curv.read_text())["scalars"])
            self.assertIn("gravitational_constant_si_Z2Sigma", json.loads(out_g.read_text())["scalars"])

    def test_forbidden_provenance_blocks_h0_writer(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "h0.json"
            path.write_text(
                json.dumps(_payload("H0_Z2Sigma_km_s_Mpc", "H0_Z2Sigma", 70.0, "Planck")),
                encoding="utf-8",
            )
            payload = build_h0(input_path=path, output_path=Path(tmp) / "out.json")
        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
