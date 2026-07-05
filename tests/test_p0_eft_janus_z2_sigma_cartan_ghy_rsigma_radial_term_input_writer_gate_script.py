import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_radial_term_input_writer_gate import (
    build_payload,
)


def _input(provenance: str = "active Cartan-GHY radial variation") -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "radial_embedding_variation_evaluated": True,
        "a_grid": [0.5, 1.0],
        "E_CartanGHY": [1.0, 2.0],
        "E_CartanGHY_provenance": provenance,
    }


class CartanGHYRSigmaRadialTermInputWriterGateTests(unittest.TestCase):
    def test_active_input_writes_radial_term_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "cartan_input.json"
            output_path = root / "rsigma_E_CartanGHY.json"
            input_path.write_text(json.dumps(_input()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(written["term_name"], "E_CartanGHY")
        self.assertEqual(written["term_values"], [1.0, 2.0])

    def test_missing_radial_variation_or_forbidden_provenance_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "cartan_input.json"
            output_path = root / "rsigma_E_CartanGHY.json"
            bad = _input("Planck LCDM fit")
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "cartan_input.json"
            bad = _input()
            bad["radial_embedding_variation_evaluated"] = False
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("radial_embedding_variation_evaluated", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
