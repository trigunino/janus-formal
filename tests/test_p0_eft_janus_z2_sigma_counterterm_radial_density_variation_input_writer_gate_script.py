import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_density_variation_input_writer_gate import (
    build_payload,
)


def _geometry(**overrides):
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
        "geometry_factors_ready": True,
        "dimension": 3,
        "sqrt_det_unit_q": 2.0,
    }
    payload.update(overrides)
    return payload


def _profile(**overrides):
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
        "L_ct_profile_ready": True,
        "a_grid": [0.5, 1.0],
        "R_Sigma_values": [2.0, 3.0],
        "L_ct_values": [7.0, 11.0],
        "partial_R_L_ct_values": [13.0, 17.0],
    }
    payload.update(overrides)
    return payload


class CountertermRadialDensityVariationInputWriterGateTests(unittest.TestCase):
    def test_writes_density_variation_inputs_from_geometry_and_profile(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            geometry = root / "geometry.json"
            profile = root / "profile.json"
            output = root / "out.json"
            geometry.write_text(json.dumps(_geometry()), encoding="utf-8")
            profile.write_text(json.dumps(_profile()), encoding="utf-8")

            payload = build_payload(
                geometry_path=geometry,
                profile_path=profile,
                output_path=output,
            )
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["counterterm_density_explicit"])
        self.assertTrue(written["radial_variation_ready"])
        self.assertEqual(written["sqrt_abs_h_values"], [16.0, 54.0])
        self.assertEqual(written["partial_R_sqrt_abs_h_values"], [24.0, 54.0])
        self.assertEqual(written["L_ct_values"], [7.0, 11.0])
        self.assertEqual(written["partial_R_L_ct_values"], [13.0, 17.0])

    def test_forbidden_fitted_counterterm_coefficient_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            geometry = root / "geometry.json"
            profile = root / "profile.json"
            geometry.write_text(json.dumps(_geometry()), encoding="utf-8")
            profile.write_text(
                json.dumps(_profile(fitted_counterterm_coefficient_used=True)),
                encoding="utf-8",
            )

            payload = build_payload(
                geometry_path=geometry,
                profile_path=profile,
                output_path=root / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])

    def test_missing_profile_blocks_on_lct_profile(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            geometry = root / "geometry.json"
            geometry.write_text(json.dumps(_geometry()), encoding="utf-8")

            payload = build_payload(
                geometry_path=geometry,
                profile_path=root / "missing.json",
                output_path=root / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "counterterm_lct_radial_profile")


if __name__ == "__main__":
    unittest.main()
