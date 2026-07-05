import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rp3_spatial_slice_curvature_sign_gate import (
    build_payload,
)


def _rp3_payload(*, quotient: str = "RP3", provenance: str = "active_projective_spatial_slice") -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_curvature_fit_used": False,
        "spatial_topology": {
            "cover_spatial_slice": "S3",
            "quotient_spatial_slice": quotient,
            "antipodal_Z2_quotient": True,
        },
        "topology_provenance": {
            "quotient_spatial_slice": provenance,
        },
    }


class P0EFTJanusZ2SigmaRP3SpatialSliceCurvatureSignGateTests(unittest.TestCase):
    def test_missing_input_blocks_gate_but_rule_is_ready(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["rp3_spatial_slice_to_k_plus_one_rule_ready"])
        self.assertTrue(payload["curvature_radius_still_required"])

    def test_valid_rp3_slice_writes_k_plus_one(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "rp3.json"
            output_path = tmpdir / "sign.json"
            input_path.write_text(json.dumps(_rp3_payload()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["scalars"]["k_Z2Sigma"], 1)
        self.assertTrue(written["sign_policy"]["curvature_radius_still_required"])
        self.assertFalse(written["archived_z4_background_reuse_used"])

    def test_non_rp3_slice_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "rp3.json"
            input_path.write_text(json.dumps(_rp3_payload(quotient="R3")), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=tmpdir / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("quotient_spatial_slice must be RP3", payload["validation_error"])

    def test_forbidden_provenance_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "rp3.json"
            input_path.write_text(
                json.dumps(_rp3_payload(provenance="Planck LCDM")),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=tmpdir / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
