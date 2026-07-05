import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_deltaK_input_writer_gate import (
    build_payload,
)


def _grid_payload(provenance="active tunnel embedding extrinsic curvature grid") -> dict:
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


class P0EFTJanusZ2SigmaCartanGHYDeltaKInputWriterGateTests(unittest.TestCase):
    def test_missing_grid_blocks_writer(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                output_path=Path(tmp) / "deltaK.json",
            )
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["deltaK_input_written"])

    def test_active_grid_writes_deltaK_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "grid.json"
            output_path = Path(tmp) / "deltaK.json"
            input_path.write_text(json.dumps(_grid_payload()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["DeltaK_s_Z2Sigma"], [2.0, 4.0, 8.0])
        self.assertEqual(written["DeltaK_tau_Z2Sigma"], [3.0, 6.0, 12.0])
        self.assertEqual(written["z2_orientation_sign"], -1.0)
        self.assertFalse(written["archived_z4_reuse_used"])

    def test_forbidden_provenance_blocks_writer(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "grid.json"
            output_path = Path(tmp) / "deltaK.json"
            input_path.write_text(
                json.dumps(_grid_payload(provenance="Planck LCDM")),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
