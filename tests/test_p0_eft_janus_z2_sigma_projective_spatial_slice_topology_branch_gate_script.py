import unittest
import json
import tempfile
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_projective_spatial_slice_topology_branch_gate import (
    build_payload,
)


def _input_payload(action: str) -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_curvature_fit_used": False,
        "time_gauge_leaf_action": {
            "z2_equivariant_time_gauge_derived": True,
            "flrw_slices_from_active_time_gauge": True,
            "leaf_action_type": action,
        },
    }


class ProjectiveSpatialSliceTopologyBranchGateTests(unittest.TestCase):
    def test_declares_rp3_and_s3_paired_branches_without_selecting(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertTrue(payload["positive_curvature_sign_supported"])
        self.assertEqual(
            payload["rp3_single_invariant_leaf_branch"]["volume_factor_pi2_R3"],
            1.0,
        )
        self.assertEqual(
            payload["s3_paired_leaf_representative_branch"]["volume_factor_pi2_R3"],
            2.0,
        )
        self.assertTrue(payload["time_parity_to_leaf_action_rule_ready"])
        self.assertIn(payload["time_gauge_leaf_action_input_writer_passed"], [True, False])
        self.assertFalse(payload["topology_branch_selected"])
        self.assertFalse(payload["gate_passed"])

    def test_invariant_leaf_input_selects_rp3_and_writes_k_plus_one(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "time_gauge.json"
            output_path = tmpdir / "sign.json"
            input_path.write_text(
                json.dumps(_input_payload("antipodal_invariant_leaf")),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["selected_spatial_topology_branch"], "RP3")
        self.assertEqual(written["scalars"]["k_Z2Sigma"], 1)
        self.assertEqual(written["spatial_topology"]["volume_factor_pi2_R3"], 1.0)

    def test_paired_leaf_input_selects_s3_representative(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "time_gauge.json"
            output_path = tmpdir / "sign.json"
            input_path.write_text(
                json.dumps(_input_payload("antipodal_paired_leaves")),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(
            payload["selected_spatial_topology_branch"],
            "S3_paired_leaf_representative",
        )
        self.assertEqual(
            written["spatial_topology"]["quotient_spatial_slice"],
            "S3_paired_leaf_representative",
        )
        self.assertEqual(written["spatial_topology"]["volume_factor_pi2_R3"], 2.0)

    def test_no_external_background_or_archive(self):
        payload = build_payload()

        self.assertFalse(payload["uses_compressed_planck_lcdm_background"])
        self.assertFalse(payload["uses_archived_z4_background"])
        self.assertFalse(payload["uses_observational_curvature_fit"])


if __name__ == "__main__":
    unittest.main()
