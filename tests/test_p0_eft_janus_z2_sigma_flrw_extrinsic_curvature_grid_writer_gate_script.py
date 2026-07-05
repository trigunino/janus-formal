import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_grid_writer_gate import (
    build_payload,
)


def _payload(provenance="active tunnel embedding extrinsic curvature grid") -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.25, 0.5, 1.0],
        "K_s_plus_Z2Sigma": [3.0, 6.0, 12.0],
        "K_s_minus_Z2Sigma": [1.0, 2.0, 4.0],
        "K_tau_plus_Z2Sigma": [5.0, 10.0, 20.0],
        "K_tau_minus_Z2Sigma": [2.0, 4.0, 8.0],
        "z2_orientation_sign": -1.0,
        "K_provenance": provenance,
    }


class P0EFTJanusZ2SigmaFLRWExtrinsicCurvatureGridWriterGateTests(unittest.TestCase):
    def test_missing_inputs_block_writer(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                output_path=Path(tmp) / "grid.json",
            )
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["flrw_extrinsic_curvature_grid_written"])

    def test_valid_active_inputs_write_grid(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "inputs.json"
            output_path = Path(tmp) / "grid.json"
            input_path.write_text(json.dumps(_payload()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["flrw_extrinsic_curvature_grid_written"])
        self.assertEqual(written["K_s_plus_Z2Sigma"], [3.0, 6.0, 12.0])
        self.assertFalse(payload["active_tunnel_embedding_of_a_closure_ready"])
        self.assertTrue(payload["input_active_derived_manifest_is_authoritative"])

    def test_forbidden_provenance_blocks_writer(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "inputs.json"
            output_path = Path(tmp) / "grid.json"
            input_path.write_text(
                json.dumps(_payload(provenance="archived Z4")),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
