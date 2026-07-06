from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_projection_input_writer_gate import (
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


class SurfaceHKProjectionInputWriterGateTests(unittest.TestCase):
    def test_missing_inputs_block(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                geometry_path=Path(tmp) / "geometry.json",
                coefficient_path=Path(tmp) / "coeff.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["primary_blocker"],
            "surface_hk_radial_geometry_inputs_and_active_density_coefficients",
        )

    def test_writes_projection_inputs_from_active_geometry_and_coefficients(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            geometry_path = root / "geometry.json"
            coefficient_path = root / "coeff.json"
            output_path = root / "output.json"
            geometry_path.write_text(
                json.dumps(
                    _active(
                        a_grid=[1.0],
                        R_Sigma_values=[2.0],
                        sqrt_abs_h_values=[8.0],
                        K_tau_values=[5.0],
                        K_s_values=[7.0],
                        partial_R_h_tau_values=[10.0],
                        partial_R_h_s_values=[14.0],
                        partial_R_K_tau_values=[1.0],
                        partial_R_K_s_values=[2.0],
                    )
                ),
                encoding="utf-8",
            )
            coefficient_path.write_text(
                json.dumps(
                    _active(
                        a_grid=[1.0],
                        a0_values=[1.0],
                        a1_values=[2.0],
                        a2_values=[3.0],
                        a3_values=[4.0],
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                geometry_path=geometry_path,
                coefficient_path=coefficient_path,
                output_path=output_path,
            )
            output = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(output["K_trace_values"], [16.0])
        self.assertEqual(output["L_Sigma_values"], [1489.0])
        self.assertEqual(output["alpha_K_tau_values"], [-58.0])
        self.assertEqual(output["alpha_K_s_values"], [154.0])


if __name__ == "__main__":
    unittest.main()
