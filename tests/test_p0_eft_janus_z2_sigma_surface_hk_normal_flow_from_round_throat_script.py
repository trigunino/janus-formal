import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_surface_hk_normal_flow_from_round_throat import (
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


class SurfaceHKNormalFlowFromRoundThroatTests(unittest.TestCase):
    def test_writes_round_throat_normal_flow_geometry(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q = root / "q.json"
            radius = root / "radius.json"
            output = root / "out.json"
            q.write_text(
                json.dumps(_active(unit_intrinsic_metric_q_ab=[[1, 0, 0], [0, 1, 0], [0, 0, 1]])),
                encoding="utf-8",
            )
            radius.write_text(
                json.dumps(
                    _active(
                        round_throat_radius_grid_ready=True,
                        a_grid=[0.5],
                        R_Sigma_values=[2.0],
                        normal_orientation_sign=-1.0,
                    )
                ),
                encoding="utf-8",
            )

            payload = build_payload(q_path=q, radius_path=radius, output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["induced_metric_h_ab"][0][0][0], -1.0)
        self.assertEqual(written["induced_metric_h_ab"][0][1][1], 4.0)
        self.assertEqual(written["extrinsic_curvature_K_ab"][0][1][1], -2.0)
        self.assertEqual(written["normal_riemann_R_nabn"][0][1][1], 0.0)

    def test_missing_radius_grid_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            q = root / "q.json"
            q.write_text(
                json.dumps(_active(unit_intrinsic_metric_q_ab=[[1, 0, 0], [0, 1, 0], [0, 0, 1]])),
                encoding="utf-8",
            )

            payload = build_payload(q_path=q, radius_path=root / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "surface_hk_round_throat_radius_grid_inputs")


if __name__ == "__main__":
    unittest.main()
