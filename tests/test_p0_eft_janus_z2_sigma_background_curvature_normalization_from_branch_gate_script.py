import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_background_curvature_normalization_from_branch_gate import (
    build_payload,
)


def _branch_payload(provenance: str = "active_flrw_spatial_metric_branch") -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {
            "H0_Z2Sigma_km_s_Mpc": 70.0,
            "R_curv_Z2Sigma_Mpc": 3000.0,
            "k_Z2Sigma": -1,
        },
        "scalar_provenance": {
            "H0_Z2Sigma": "active_background_scale_gate",
            "R_curv_Z2Sigma": provenance,
            "k_Z2Sigma": provenance,
        },
    }


class P0EFTJanusZ2SigmaBackgroundCurvatureNormalizationFromBranchGateTests(unittest.TestCase):
    def test_missing_input_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["input_exists"])
        self.assertTrue(payload["computes_omega_k_from_k_Rcurv_H0"])
        self.assertFalse(payload["background_curvature_normalization_input_written"])
        self.assertFalse(payload["gate_passed"])

    def test_valid_branch_input_writes_omega_k_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "branch.json"
            output_path = tmpdir / "curvature_norm.json"
            input_path.write_text(json.dumps(_branch_payload()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["background_curvature_normalization_input_written"])
        self.assertGreater(payload["omega_k_Z2Sigma_value"], 0.0)
        self.assertIn("omega_k_Z2Sigma", written["scalars"])
        self.assertFalse(written["compressed_planck_lcdm_background_used"])
        self.assertFalse(written["archived_z4_background_reuse_used"])

    def test_forbidden_provenance_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "branch.json"
            input_path.write_text(json.dumps(_branch_payload("Planck LCDM")), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=tmpdir / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
