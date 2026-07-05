import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_transparency_gate import (
    build_payload,
)


class RSigmaMatterFluxRadialTermFromTransparencyGateTests(unittest.TestCase):
    def test_writes_zero_radial_term_from_transparency(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "transparency.json"
            output_path = root / "matter.json"
            input_path.write_text(
                json.dumps({
                    "active_core": "Z2_tunnel_Sigma",
                    "source": "active_derived",
                    "active_sigma_transparency_derived": True,
                    "a_grid": [0.25, 0.5, 1.0],
                    "compressed_planck_lcdm_background_used": False,
                    "archived_z4_reuse_used": False,
                    "phenomenological_holst_bao_scan_used": False,
                }),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["term_name"], "E_matterFlux")
        self.assertEqual(written["term_values"], [0.0, 0.0, 0.0])

    def test_transparency_false_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "transparency.json"
            input_path.write_text(
                json.dumps({
                    "active_core": "Z2_tunnel_Sigma",
                    "source": "active_derived",
                    "active_sigma_transparency_derived": False,
                    "a_grid": [0.25, 0.5, 1.0],
                    "compressed_planck_lcdm_background_used": False,
                    "archived_z4_reuse_used": False,
                    "phenomenological_holst_bao_scan_used": False,
                }),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("active_sigma_transparency_derived", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
