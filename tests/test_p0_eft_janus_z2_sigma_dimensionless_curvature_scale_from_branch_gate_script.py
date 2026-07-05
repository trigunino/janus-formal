import json
import tempfile
import unittest
from pathlib import Path

from janus_lab.constants import SPEED_OF_LIGHT_KM_S
from scripts.build_p0_eft_janus_z2_sigma_dimensionless_curvature_scale_from_branch_gate import (
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
            "k_Z2Sigma": 1,
        },
        "scalar_provenance": {
            "H0_Z2Sigma": "active_background_scale_gate",
            "R_curv_Z2Sigma": provenance,
            "k_Z2Sigma": provenance,
        },
    }


class DimensionlessCurvatureScaleFromBranchGateTests(unittest.TestCase):
    def test_missing_input_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["input_exists"])
        self.assertFalse(payload["gate_passed"])

    def test_valid_branch_input_writes_scale_normalization(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "branch.json"
            output_path = root / "scale_norm.json"
            input_path.write_text(json.dumps(_branch_payload()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        expected = 70.0 * 3000.0 / SPEED_OF_LIGHT_KM_S
        self.assertTrue(payload["gate_passed"])
        self.assertAlmostEqual(payload["h0_R_curv_over_c_value"], expected)
        self.assertAlmostEqual(
            written["scalars"]["h0_R_curv_over_c_Z2Sigma"],
            expected,
        )
        self.assertFalse(written["observational_H0_fit_used"])
        self.assertFalse(written["observational_curvature_fit_used"])

    def test_forbidden_provenance_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "branch.json"
            input_path.write_text(json.dumps(_branch_payload("Planck LCDM")), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
