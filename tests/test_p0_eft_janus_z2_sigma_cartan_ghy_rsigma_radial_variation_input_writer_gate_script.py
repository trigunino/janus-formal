import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_radial_variation_input_writer_gate import (
    build_payload,
)


def _input() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.5, 1.0],
        "sqrt_abs_h": [2.0, 3.0],
        "K_trace": [4.0, 5.0],
        "partial_R_K_trace": [1.0, 2.0],
        "trace_h_inv_partial_R_h": [0.5, 0.25],
        "z2_orientation_sign": 1.0,
        "kappa_Z2Sigma": 2.0,
        "E_CartanGHY_provenance": "active Cartan-GHY radial variation",
    }


class CartanGHYRSigmaRadialVariationInputWriterGateTests(unittest.TestCase):
    def test_active_primitives_write_cartan_ghy_radial_term_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "variation_input.json"
            output_path = root / "cartan_term_input.json"
            input_path.write_text(json.dumps(_input()), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertTrue(written["radial_embedding_variation_evaluated"])
        self.assertEqual(written["E_CartanGHY"], [2.0, 3.9375])

    def test_forbidden_flag_or_bad_kappa_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "variation_input.json"
            bad = _input()
            bad["observational_H0_fit_used"] = True
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("observational_H0_fit_used", payload["validation_error"])

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "variation_input.json"
            bad = _input()
            bad["kappa_Z2Sigma"] = 0.0
            input_path.write_text(json.dumps(bad), encoding="utf-8")

            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn("kappa_Z2Sigma", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
