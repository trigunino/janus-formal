import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_dimensionless_curvature_scale_input_writer_gate import (
    build_payload,
)


def _input(value: float = 2.0, provenance: str = "active_tunnel_embedding_scale") -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {"h0_R_curv_over_c_Z2Sigma": value},
        "scalar_provenance": {"h0_R_curv_over_c_Z2Sigma": provenance},
    }


class DimensionlessCurvatureScaleInputWriterGateTests(unittest.TestCase):
    def test_missing_input_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                output_path=Path(tmp) / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["dimensionless_curvature_scale_input_written"])

    def test_valid_input_writes_scale_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "input.json"
            output_path = tmpdir / "scale.json"
            input_path.write_text(json.dumps(_input()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            output = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["h0_R_curv_over_c_value"], 2.0)
        self.assertEqual(output["scalars"]["h0_R_curv_over_c_Z2Sigma"], 2.0)
        self.assertFalse(output["observational_H0_fit_used"])
        self.assertFalse(output["observational_curvature_fit_used"])

    def test_forbidden_fit_or_provenance_blocks_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            bad_fit = _input()
            bad_fit["observational_curvature_fit_used"] = True
            input_path = tmpdir / "bad_fit.json"
            input_path.write_text(json.dumps(bad_fit), encoding="utf-8")
            payload = build_payload(input_path=input_path, output_path=tmpdir / "out.json")
            self.assertFalse(payload["gate_passed"])
            self.assertIn("observational_curvature_fit_used", payload["validation_error"])

            bad_provenance = tmpdir / "bad_provenance.json"
            bad_provenance.write_text(
                json.dumps(_input(provenance="Planck LCDM curvature")),
                encoding="utf-8",
            )
            payload = build_payload(
                input_path=bad_provenance,
                output_path=tmpdir / "out2.json",
            )
            self.assertFalse(payload["gate_passed"])
            self.assertIn("Forbidden", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
