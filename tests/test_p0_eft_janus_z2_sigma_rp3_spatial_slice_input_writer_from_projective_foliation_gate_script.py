import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rp3_spatial_slice_input_writer_from_projective_foliation_gate import (
    build_payload,
)


def _valid_input(**overrides):
    foliation = {
        "ambient_cover": "S4",
        "ambient_quotient": "RP4",
        "spatial_cover_leaf": "S3",
        "spatial_quotient_leaf": "RP3",
        "antipodal_action_preserves_spatial_leaf": True,
        "spatial_leaf_action_free": True,
        "flrw_slices_identified_with_spatial_leaves": True,
    }
    foliation.update(overrides.pop("projective_foliation", {}))
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_curvature_fit_used": False,
        "projective_foliation": foliation,
    }
    payload.update(overrides)
    return payload


class RP3SpatialSliceInputWriterFromProjectiveFoliationGateTests(unittest.TestCase):
    def test_missing_input_blocks_but_rule_ready(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["projective_foliation_to_rp3_slice_rule_ready"])
        self.assertTrue(payload["requires_active_foliation_not_topology_alone"])
        self.assertFalse(payload["projective_foliation_compatibility_gate_passed"])
        self.assertFalse(payload["single_leaf_RP3_inference_allowed"])

    def test_valid_foliation_writes_rp3_slice_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "foliation.json"
            output_path = tmpdir / "rp3.json"
            input_path.write_text(json.dumps(_valid_input()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["spatial_topology"]["cover_spatial_slice"], "S3")
        self.assertEqual(written["spatial_topology"]["quotient_spatial_slice"], "RP3")
        self.assertTrue(written["open_quantities"]["R_curv_Z2Sigma_still_required"])

    def test_missing_flrw_leaf_identification_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "foliation.json"
            input_path.write_text(
                json.dumps(_valid_input(projective_foliation={
                    "flrw_slices_identified_with_spatial_leaves": False,
                })),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=tmpdir / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("flrw_slices_identified", payload["validation_error"])

    def test_forbidden_provenance_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "foliation.json"
            input_path.write_text(
                json.dumps(_valid_input(archived_z4_background_reuse_used=True)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=tmpdir / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
