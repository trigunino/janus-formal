import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_background_curvature_radius_input_writer_gate import (
    build_payload,
)


def _payload(value: float = 3000.0, provenance: str = "active_embedding_scale") -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {"R_curv_Z2Sigma_Mpc": value},
        "scalar_provenance": {"R_curv_Z2Sigma": provenance},
    }


class BackgroundCurvatureRadiusInputWriterGateTests(unittest.TestCase):
    def test_missing_input_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "active_R_curv_scale_normalization_from_RSigma")
        self.assertFalse(payload["background_curvature_radius_input_written"])
        self.assertEqual(payload["missing_active_artifact"], str(Path(tmp) / "missing.json"))
        self.assertTrue(payload["requires_active_curvature_radius_scale_normalization"])
        self.assertTrue(payload["requires_active_embedding_or_throat_radius_scale"])
        self.assertTrue(payload["dimensionless_H0R_over_c_insufficient_for_R_curv"])
        self.assertEqual(
            payload["normalization_source_frontier"]["source_gate"],
            "P0EFTJanusZ2SigmaRSigmaSolutionToEmbeddingCurvatureBranchGate",
        )
        self.assertIn(
            "matter_flux_radial_block",
            payload["normalization_source_frontier"]["blocks"],
        )

    def test_valid_input_writes_radius_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "radius.json"
            output_path = tmpdir / "out.json"
            input_path.write_text(json.dumps(_payload()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            output = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(payload["R_curv_Z2Sigma_Mpc_value"], 3000.0)
        self.assertEqual(output["scalars"]["R_curv_Z2Sigma_Mpc"], 3000.0)
        self.assertFalse(output["observational_H0_fit_used"])

    def test_forbidden_or_nonpositive_input_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            bad_fit_path = tmpdir / "bad_fit.json"
            bad_fit = _payload()
            bad_fit["observational_curvature_fit_used"] = True
            bad_fit_path.write_text(json.dumps(bad_fit), encoding="utf-8")
            payload = build_payload(input_path=bad_fit_path, output_path=tmpdir / "out.json")
            self.assertFalse(payload["gate_passed"])
            self.assertIn("observational_curvature_fit_used", payload["validation_error"])

            bad_value_path = tmpdir / "bad_value.json"
            bad_value_path.write_text(json.dumps(_payload(value=0.0)), encoding="utf-8")
            payload = build_payload(input_path=bad_value_path, output_path=tmpdir / "out2.json")
            self.assertFalse(payload["gate_passed"])
            self.assertIn("must be positive", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
