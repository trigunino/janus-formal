from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_sigma_riccati_normal_flow_to_surface_hk_geometry_gate import (
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


class RiccatiNormalFlowToSurfaceHKGeometryGateTests(unittest.TestCase):
    def test_missing_input_blocks(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "surface_hk_normal_flow_geometry_inputs")

    def test_writes_tensor_geometry_from_riccati_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "input.json"
            output_path = root / "output.json"
            input_path.write_text(
                json.dumps(
                    _active(
                        a_grid=[1.0],
                        R_Sigma_values=[2.0],
                        induced_metric_h_ab=[[[1.0, 0.0], [0.0, 4.0]]],
                        extrinsic_curvature_K_ab=[[[2.0, 0.0], [0.0, 8.0]]],
                        normal_riemann_R_nabn=[[[3.0, 0.0], [0.0, 5.0]]],
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)
            output = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(output["partial_R_induced_metric_h_ab"], [[[4.0, 0.0], [0.0, 16.0]]])
        self.assertEqual(output["partial_R_extrinsic_curvature_K_ab"], [[[7.0, 0.0], [0.0, 21.0]]])


if __name__ == "__main__":
    unittest.main()
