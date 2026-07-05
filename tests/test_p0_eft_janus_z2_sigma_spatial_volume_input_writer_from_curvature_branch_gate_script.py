import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_spatial_volume_input_writer_from_curvature_branch_gate import (
    build_payload,
)


def _branch_payload(
    *,
    k_value: int = 1,
    provenance: str = "active_flrw_spatial_metric_branch",
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
            "H0_Z2Sigma_km_s_Mpc": 70.0,
            "R_curv_Z2Sigma_Mpc": 2.0,
            "k_Z2Sigma": k_value,
        },
        "scalar_provenance": {
            "H0_Z2Sigma": "active_background_scale_gate",
            "R_curv_Z2Sigma": provenance,
            "k_Z2Sigma": provenance,
        },
        "spatial_topology": {
            "quotient_spatial_slice": quotient,
        },
    }


class P0EFTJanusZ2SigmaSpatialVolumeInputWriterFromCurvatureBranchGateTests(unittest.TestCase):
    def test_missing_input_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "active_curvature_branch_manifest")
        self.assertTrue(payload["Mpc_to_m_conversion_declared"])
        self.assertEqual(
            payload["nearest_missing_artifact"],
            str(Path(tmp) / "missing.json"),
        )
        self.assertEqual(
            payload["nearest_spatial_volume_input_frontier"]["nearest_missing_artifact"],
            str(Path(tmp) / "missing.json"),
        )
        self.assertIn(
            "active_R_curv_Z2Sigma_Mpc_from_embedding_or_throat_scale",
            payload["nearest_spatial_volume_input_frontier"]["blocks"],
        )
        self.assertTrue(payload["dimensionless_H0R_over_c_insufficient_for_physical_volume"])

    def test_valid_closed_branch_writes_volume_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "branch.json"
            output_path = tmpdir / "volume_input.json"
            input_path.write_text(json.dumps(_branch_payload()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))
            output_exists = output_path.exists()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertTrue(output_exists)
        self.assertEqual(written["scalars"]["k_Z2Sigma"], 1)
        self.assertFalse(payload["curvature_branch_inputs_assembler_passed"])
        self.assertTrue(payload["input_active_derived_manifest_is_authoritative"])
        self.assertEqual(payload["nearest_spatial_volume_input_frontier"]["blocks"], [])
        self.assertIn(
            "derive_active_R_curv_Z2Sigma_Mpc_not_from_scale_free_BAO_fit",
            payload["next_required"],
        )

    def test_paired_leaf_topology_writes_volume_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "branch.json"
            output_path = tmpdir / "volume_input.json"
            input_path.write_text(
                json.dumps(_branch_payload(quotient="S3_paired_leaf_representative")),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)
            output_exists = output_path.exists()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(output_exists)

    def test_open_or_flat_branch_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "branch.json"
            input_path.write_text(json.dumps(_branch_payload(k_value=-1)), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=tmpdir / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("k_Z2Sigma = +1", payload["validation_error"])

    def test_forbidden_provenance_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "branch.json"
            input_path.write_text(
                json.dumps(_branch_payload(provenance="Planck LCDM")),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=tmpdir / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
