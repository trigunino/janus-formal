import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_effective_dimensional_anchor_pipeline_gate import (
    build_payload,
)
from scripts.write_p0_eft_janus_z2_sigma_effective_dimensional_anchor_input import (
    build_payload as build_anchor_payload,
)


def _write_sign(path: Path) -> None:
    path.write_text(
        json.dumps(
            {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_background_reuse_used": False,
                "observational_curvature_fit_used": False,
                "scalars": {"k_Z2Sigma": 1},
                "scalar_provenance": {
                    "k_Z2Sigma": "active_time_gauge_antipodal_paired_leaves"
                },
            }
        ),
        encoding="utf-8",
    )


class EffectiveDimensionalAnchorPipelineGateTests(unittest.TestCase):
    def test_live_pipeline_blocks_without_dimensional_anchor_manifests(self):
        payload = build_payload()

        self.assertFalse(payload["pipeline_ready"])
        self.assertEqual(payload["primary_blocker"], "h0_input")
        self.assertFalse(payload["full_no_fit_prediction_ready"])

    def test_pipeline_runs_when_effective_h0_and_radius_are_supplied(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            h0_norm = root / "h0_norm.json"
            radius_norm = root / "radius_norm.json"
            h0_input = root / "h0.json"
            radius_input = root / "radius.json"
            sign_input = root / "sign.json"
            scale_norm = root / "scale_norm.json"
            scale_input = root / "scale.json"
            omega = root / "omega.json"
            anchors = build_anchor_payload(
                h0_km_s_mpc=70.0,
                r_curv_mpc=3000.0,
                provenance="declared_boundary_state_scale",
            )
            h0_norm.write_text(
                json.dumps(anchors["anchors"]["H0_Z2Sigma"]),
                encoding="utf-8",
            )
            radius_norm.write_text(
                json.dumps(anchors["anchors"]["R_curv_Z2Sigma"]),
                encoding="utf-8",
            )
            _write_sign(sign_input)

            payload = build_payload(
                h0_norm_path=h0_norm,
                radius_norm_path=radius_norm,
                h0_input_path=h0_input,
                radius_input_path=radius_input,
                sign_input_path=sign_input,
                scale_norm_path=scale_norm,
                scale_input_path=scale_input,
                omega_output_path=omega,
            )
            omega_payload = json.loads(omega.read_text(encoding="utf-8"))

        self.assertTrue(payload["pipeline_ready"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertIn("omega_k_Z2Sigma", omega_payload["scalars"])


if __name__ == "__main__":
    unittest.main()
