from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_sigma_holst_palatini_boundary_theta_pt67_projection import (
    build_payload,
    render_markdown,
)
from scripts.write_p0_eft_janus_z2_pt67_regular_sigma_hk_inputs import (
    build_payload as build_pt67_hk,
)


def _torsion_zero() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "torsion_T_internal_I_ab": [
            [[0.0, 0.0], [0.0, 0.0]],
            [[0.0, 0.0], [0.0, 0.0]],
        ],
    }


class HolstPalatiniBoundaryThetaPT67ProjectionTests(unittest.TestCase):
    def test_projection_eliminates_non_ghy_traces_but_does_not_unblock_counterterm(self):
        with tempfile.TemporaryDirectory() as tmp:
            pt67 = Path(tmp) / "pt67.json"
            torsion = Path(tmp) / "torsion.json"
            output = Path(tmp) / "projection.json"
            pt67.write_text(json.dumps(build_pt67_hk()), encoding="utf-8")
            torsion.write_text(json.dumps(_torsion_zero()), encoding="utf-8")

            payload = build_payload(
                pt67_hk_path=pt67,
                torsion_path=torsion,
                output_path=output,
            )
            projection = payload["projection"]

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(projection["R_h_trace_values"], [0.0, 0.0, 0.0])
        self.assertEqual(projection["R_K_trace_values"], [0.0, 0.0, 0.0])
        self.assertFalse(projection["counterterm_component_unblocked"])
        self.assertIn("independent Sigma surface-action", projection["why_not_unblocked"])

    def test_missing_inputs_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                pt67_hk_path=Path(tmp) / "missing_pt67.json",
                torsion_path=Path(tmp) / "missing_torsion.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("pt67_regular_sigma_hk_inputs", payload["next_required"])

    def test_markdown_reports_trace_zero(self):
        markdown = render_markdown(
            {
                "gate_passed": True,
                "validation_error": None,
                "projection": {
                    "projection_result": {
                        "Palatini_boundary_channel": "Cartan_GHY_or_junction_partition",
                        "Holst_boundary_channel": "torsionless_zero_or_exact_form_only",
                        "non_GHY_metric_trace_R_h_from_theta": "0",
                        "non_GHY_extrinsic_trace_R_K_from_theta": "0",
                    },
                    "why_not_unblocked": "not enough",
                },
            }
        )

        self.assertIn("R_h trace from theta: `0`", markdown)
        self.assertIn("R_K trace from theta: `0`", markdown)


if __name__ == "__main__":
    unittest.main()
