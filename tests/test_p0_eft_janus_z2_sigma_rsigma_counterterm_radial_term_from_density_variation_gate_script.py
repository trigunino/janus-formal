import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rsigma_counterterm_radial_term_from_density_variation_gate import (
    build_payload,
)


def _source(**overrides):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "counterterm_density_explicit": True,
        "radial_variation_ready": True,
        "a_grid": [0.5, 1.0],
        "sqrt_abs_h_values": [2.0, 3.0],
        "partial_R_sqrt_abs_h_values": [0.5, 0.25],
        "L_ct_values": [7.0, 11.0],
        "partial_R_L_ct_values": [13.0, 17.0],
    }
    payload.update(overrides)
    return payload


class RSigmaCountertermRadialTermFromDensityVariationGateTests(unittest.TestCase):
    def test_writes_radial_counterterm_from_density_variation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source.json"
            output = root / "counterterm.json"
            source.write_text(json.dumps(_source()), encoding="utf-8")

            payload = build_payload(input_path=source, output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["term_name"], "E_counterterm")
        self.assertEqual(written["term_values"], [29.5, 53.75])

    def test_forbidden_fitted_coefficient_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source.json"
            source.write_text(
                json.dumps(_source(fitted_counterterm_coefficient_used=True)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])

    def test_missing_input_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "counterterm_radial_density_variation_inputs")


if __name__ == "__main__":
    unittest.main()
