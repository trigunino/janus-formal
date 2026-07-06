from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_alpha_radial_projection_gate import (
    build_payload,
)


def _active(**fields):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
    }
    payload.update(fields)
    return payload


class SurfaceHKAlphaRadialProjectionGateTests(unittest.TestCase):
    def test_missing_input_blocks(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["primary_blocker"],
            "surface_HK_alpha_components_and_radial_derivatives",
        )

    def test_writes_counterterm_alpha_radial_components(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "input.json"
            output_path = root / "output.json"
            input_path.write_text(
                json.dumps(
                    _active(
                        a_grid=[1.0],
                        R_Sigma_values=[2.0],
                        sqrt_abs_h_values=[2.0],
                        alpha_h_tau_values=[1.0],
                        alpha_h_s_values=[2.0],
                        alpha_K_tau_values=[3.0],
                        alpha_K_s_values=[4.0],
                        partial_R_h_tau_values=[5.0],
                        partial_R_h_s_values=[6.0],
                        partial_R_K_tau_values=[7.0],
                        partial_R_K_s_values=[8.0],
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)
            output = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(output["alpha_h_radial_coefficient_values"], [82.0])
        self.assertEqual(output["alpha_K_radial_coefficient_values"], [234.0])
        self.assertEqual(output["alpha_total_radial_values"], [316.0])


if __name__ == "__main__":
    unittest.main()
