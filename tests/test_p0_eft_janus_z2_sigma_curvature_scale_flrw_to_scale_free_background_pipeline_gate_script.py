import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_active_inputs import (
    load_active_z2sigma_scale_free_background_primitive_inputs,
)
from janus_lab.z2_sigma_flrw_component_manifest import (
    FLRW_COMPONENT_FIELDS,
    write_active_z2sigma_flrw_component_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_curvature_scale_flrw_to_scale_free_background_pipeline_gate import (
    build_payload,
)


def _base() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
    }


def _write_flrw(path: Path) -> None:
    a = np.geomspace(1.0e-3, 1.0, 64)
    components = {field: np.zeros_like(a) for field in FLRW_COMPONENT_FIELDS}
    components["cartan_ghy_rho"] = 0.3 / a**3
    components["counterterm_rho"] = 0.7 * np.ones_like(a)
    components["counterterm_p"] = -0.7 * np.ones_like(a)
    write_active_z2sigma_flrw_component_manifest(
        path,
        a_grid=a,
        flrw_components_over_rho_crit0=components,
        component_provenance={
            field: f"active_flrw_component::{field}" for field in FLRW_COMPONENT_FIELDS
        },
    )


class CurvatureScaleFLRWToScaleFreeBackgroundPipelineGateTests(unittest.TestCase):
    def test_missing_inputs_block_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                sign_input_path=root / "missing_sign.json",
                curvature_branch_path=root / "missing_branch.json",
                scale_normalization_path=root / "missing_scale_norm.json",
                scale_input_path=root / "missing_scale.json",
                flrw_component_path=root / "missing_flrw.json",
                omega_k_output_path=root / "omega.json",
                background_primitive_path=root / "background.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["uses_compressed_planck_lcdm_background"])
        self.assertFalse(payload["uses_archived_z4_background"])
        self.assertIn("flrw_components", payload["upstream_frontiers"])
        self.assertFalse(payload["upstream_frontiers"]["flrw_components"]["passed"])
        self.assertIn(
            "dimensionless_curvature_scale_from_branch",
            payload["upstream_frontiers"],
        )

    def test_active_dimensionless_scale_writes_background_primitive(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sign = root / "sign.json"
            scale = root / "scale.json"
            flrw = root / "flrw.json"
            omega = root / "omega.json"
            background = root / "background.json"
            sign.write_text(
                json.dumps(
                    {
                        **_base(),
                        "scalars": {"k_Z2Sigma": 1},
                        "scalar_provenance": {
                            "k_Z2Sigma": "active_projective_spatial_branch"
                        },
                    }
                ),
                encoding="utf-8",
            )
            scale.write_text(
                json.dumps(
                    {
                        **_base(),
                        "scalars": {"h0_R_curv_over_c_Z2Sigma": 7.0},
                        "scalar_provenance": {
                            "h0_R_curv_over_c_Z2Sigma": (
                                "active_tunnel_embedding_dimensionless_scale"
                            )
                        },
                    }
                ),
                encoding="utf-8",
            )
            _write_flrw(flrw)

            payload = build_payload(
                sign_input_path=sign,
                curvature_branch_path=root / "missing_branch.json",
                scale_normalization_path=root / "scale_norm.json",
                scale_input_path=scale,
                flrw_component_path=flrw,
                omega_k_output_path=omega,
                background_primitive_path=background,
            )
            primitive = load_active_z2sigma_scale_free_background_primitive_inputs(background)

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["omega_k_from_curvature_scale_passed"])
        self.assertTrue(payload["background_primitive_passed"])
        self.assertEqual(len(primitive.z_grid), 64)
        self.assertLess(primitive.omega_k_z2sigma, 0.0)


if __name__ == "__main__":
    unittest.main()
