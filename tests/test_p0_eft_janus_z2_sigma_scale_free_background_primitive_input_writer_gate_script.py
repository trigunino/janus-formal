import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from scripts.build_p0_eft_janus_z2_sigma_scale_free_background_primitive_input_writer_gate import (
    build_payload,
)


def _input() -> dict:
    z = np.geomspace(1.0, 1.0e4, 64) - 1.0
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "z_grid": z.tolist(),
        "E_Z2Sigma": np.sqrt(1.0 + z).tolist(),
        "omega_k_Z2Sigma": 0.0,
        "z_max": float(z[-1]),
        "primitive_provenance": {
            "E_Z2Sigma": "active_dimensionless_background_derivation",
            "omega_k_Z2Sigma": "active_projective_curvature_derivation",
        },
    }


class ScaleFreeBackgroundPrimitiveInputWriterGateTests(unittest.TestCase):
    def test_missing_input_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["background_primitive_written"])

    def test_valid_input_writes_background_primitive(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "input.json"
            output_path = tmpdir / "background.json"
            input_path.write_text(json.dumps(_input()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            output = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["background_primitive_valid"])
        self.assertEqual(output["manifest_kind"], "scale_free_background_primitive_inputs")
        self.assertIn("E_Z2Sigma", output)
        self.assertEqual(output["omega_k_Z2Sigma"], 0.0)

    def test_forbidden_flag_or_bad_values_block_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            bad_flag = _input()
            bad_flag["compressed_planck_lcdm_rd_used"] = True
            bad_flag_path = tmpdir / "bad_flag.json"
            bad_flag_path.write_text(json.dumps(bad_flag), encoding="utf-8")
            payload = build_payload(input_path=bad_flag_path, output_path=tmpdir / "out.json")
            self.assertFalse(payload["gate_passed"])
            self.assertIn("compressed_planck_lcdm_rd_used", payload["validation_error"])

            bad_values = _input()
            bad_values["E_Z2Sigma"][0] = 0.0
            bad_values_path = tmpdir / "bad_values.json"
            bad_values_path.write_text(json.dumps(bad_values), encoding="utf-8")
            payload = build_payload(input_path=bad_values_path, output_path=tmpdir / "out2.json")
            self.assertFalse(payload["gate_passed"])
            self.assertIn("positive", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
