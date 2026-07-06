from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_sigma_alpha_radial_components_to_trace_residual_inputs_gate import (
    build_payload,
)


def _active(**fields):
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
    }
    payload.update(fields)
    return payload


class AlphaRadialComponentsToTraceResidualInputsGateTests(unittest.TestCase):
    def test_writes_trace_inputs_from_radial_components(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "alpha.json"
            output_path = root / "trace.json"
            input_path.write_text(
                json.dumps(
                    _active(
                        a_grid=[0.5, 1.0],
                        R_Sigma_values=[2.0, 4.0],
                        sqrt_abs_h_values=[8.0, 64.0],
                        alpha_h_radial_coefficient_values=[32.0, 512.0],
                        alpha_K_radial_coefficient_values=[24.0, 128.0],
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)
            output = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(output["R_h_trace_values"], [1.0, 1.0])
        self.assertEqual(output["R_K_trace_values"], [3.0, 2.0])

    def test_missing_input_blocks(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "counterterm_alpha_res_radial_components")


if __name__ == "__main__":
    unittest.main()
