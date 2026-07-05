import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rsigma_a_grid_input_writer_gate import build_payload


def _source() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.25, 0.5, 1.0],
    }


class RSigmaAGridInputWriterGateTests(unittest.TestCase):
    def test_writes_grid_from_active_non_matter_flrw_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source.json"
            output = root / "grid.json"
            source.write_text(json.dumps(_source()), encoding="utf-8")

            payload = build_payload(source_path=source, output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["a_grid"], [0.25, 0.5, 1.0])
        self.assertFalse(written["archived_z4_background_reuse_used"])

    def test_missing_source_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(source_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "active_a_grid_from_non_matter_FLRW_inputs")


if __name__ == "__main__":
    unittest.main()
