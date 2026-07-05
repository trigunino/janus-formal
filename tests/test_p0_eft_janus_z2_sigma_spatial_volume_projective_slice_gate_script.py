import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_spatial_volume_projective_slice_gate import (
    build_payload,
)


def _input_payload(
    *,
    k_value: int = 1,
    provenance: str = "active_curvature_radius",
    quotient: str = "RP3",
) -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {
            "R_curv_Z2Sigma_m": 2.0,
            "k_Z2Sigma": k_value,
        },
        "scalar_provenance": {
            "R_curv_Z2Sigma_m": provenance,
            "k_Z2Sigma": "active_closed_projective_branch",
        },
        "spatial_topology": {
            "quotient_spatial_slice": quotient,
        },
    }


class P0EFTJanusZ2SigmaSpatialVolumeProjectiveSliceGateTests(unittest.TestCase):
    def test_missing_input_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "active_R_curv_Z2Sigma_and_k_plus_one")
        self.assertTrue(payload["closed_projective_RP3_volume_formula_ready"])
        self.assertIn("derive_active_R_curv_Z2Sigma_in_meters", payload["next_required"])

    def test_valid_closed_projective_input_writes_volume(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "volume_input.json"
            output_path = tmpdir / "volume_output.json"
            input_path.write_text(json.dumps(_input_payload()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertAlmostEqual(
            written["normalizations"]["spatial_volume0_m3_Z2Sigma"],
            math.pi**2 * 8.0,
        )
        self.assertTrue(written["volume_policy"]["z2_cover_factor_applied_once"])
        self.assertFalse(written["archived_z4_reuse_used"])

    def test_valid_paired_s3_representative_writes_full_s3_volume(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "volume_input.json"
            output_path = tmpdir / "volume_output.json"
            input_path.write_text(
                json.dumps(_input_payload(quotient="S3_paired_leaf_representative")),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertAlmostEqual(
            written["normalizations"]["spatial_volume0_m3_Z2Sigma"],
            2.0 * math.pi**2 * 8.0,
        )
        self.assertFalse(written["volume_policy"]["z2_cover_factor_applied_once"])

    def test_non_closed_branch_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "volume_input.json"
            input_path.write_text(json.dumps(_input_payload(k_value=0)), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=tmpdir / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("k_Z2Sigma = +1", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
