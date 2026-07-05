import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_flrw_component_manifest import (
    FLRW_COMPONENT_FIELDS,
    write_active_z2sigma_flrw_component_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate import (
    build_payload as build_constants_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_physical_inputs_to_scale_free_bao_chi2_gate import (
    TEMPERATURE_PATH,
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
    a = np.geomspace(1.0e-5, 1.0, 96)
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


def _curvature_branch() -> dict:
    return {
        **_base(),
        "scalars": {
            "H0_Z2Sigma_km_s_Mpc": 70.0,
            "R_curv_Z2Sigma_Mpc": 30000.0,
            "k_Z2Sigma": 1,
        },
        "scalar_provenance": {
            "H0_Z2Sigma": "active_background_scale_gate",
            "R_curv_Z2Sigma": "active_embedding_radius_gate",
            "k_Z2Sigma": "active_closed_projective_branch",
        },
        "spatial_topology": {"quotient_spatial_slice": "RP3"},
    }


class PhysicalInputsToScaleFreeBAOChi2GateTests(unittest.TestCase):
    def test_default_temperature_path_uses_firas_direct_manifest(self):
        self.assertEqual(
            TEMPERATURE_PATH.as_posix(),
            "outputs/active_z2_sigma/early_plasma_photon_temperature_firas_inputs.json",
        )

    def test_missing_inputs_block_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                h0_input_path=root / "missing_h0.json",
                radius_input_path=root / "missing_radius.json",
                sign_input_path=root / "missing_sign.json",
                scale_input_path=root / "missing_scale.json",
                flrw_component_path=root / "missing_flrw.json",
                curvature_branch_path=root / "missing_curvature.json",
                charge_path=root / "missing_charge.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["uses_compressed_planck_lcdm"])
        self.assertFalse(payload["uses_archived_z4"])
        self.assertIn("background", payload["upstream_frontiers"])
        self.assertIn("curvature_charge_plasma", payload["upstream_frontiers"])
        self.assertIn("plasma_primitive", payload["upstream_frontiers"])
        self.assertIn("dimensionful_scale_separation", payload["upstream_frontiers"])
        self.assertFalse(
            payload["upstream_frontiers"]["dimensionful_scale_separation"][
                "can_invert_product_to_H0_or_R_curv"
            ]
        )
        primitive_frontier = payload["upstream_frontiers"]["plasma_primitive"]
        self.assertIn("early_plasma_manifest", primitive_frontier["upstream_frontiers"])
        self.assertIn("active_h0_manifest", primitive_frontier["upstream_frontiers"])
        self.assertIn(
            "upstream_writer",
            primitive_frontier["upstream_frontiers"]["active_h0_manifest"],
        )
        self.assertIn(
            "early_plasma_manifest",
            primitive_frontier["nearest_frontier"]["blocks"],
        )
        self.assertIn("missing early_plasma_manifest", payload["blocker"])
        self.assertIn("physical_frontier_summary", payload)
        self.assertIn(
            "projected_baryon_number_charge_Z2Sigma",
            payload["physical_frontier_summary"]["baryon_charge"],
        )
        self.assertIn(
            "Gamma_drag_over_H0_Z2Sigma",
            payload["physical_frontier_summary"]["early_plasma"],
        )
        self.assertIn(
            "do_not_invert_H0_Rcurv_over_c_product",
            payload["physical_frontier_summary"]["curvature_volume"],
        )
        self.assertIn("do not invert H0*R_curv/c", payload["blocker"])
        self.assertTrue(payload["nearest_physical_inputs_frontier"]["diagnostic_only"])

    def test_active_physical_fixture_runs_to_scale_free_bao_chi2(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            h0 = root / "h0.json"
            radius = root / "radius.json"
            sign = root / "sign.json"
            scale = root / "scale.json"
            flrw = root / "flrw.json"
            curvature = root / "curvature.json"
            charge = root / "charge.json"
            constants = root / "constants.json"
            temperature = root / "temperature.json"

            h0.write_text(
                json.dumps(
                    {
                        **_base(),
                        "scalars": {"H0_Z2Sigma_km_s_Mpc": 70.0},
                        "scalar_provenance": {
                            "H0_Z2Sigma": "active_background_scale_gate"
                        },
                    }
                ),
                encoding="utf-8",
            )
            radius.write_text(
                json.dumps(
                    {
                        **_base(),
                        "scalars": {"R_curv_Z2Sigma_Mpc": 30000.0},
                        "scalar_provenance": {
                            "R_curv_Z2Sigma": "active_embedding_radius_gate"
                        },
                    }
                ),
                encoding="utf-8",
            )
            sign.write_text(
                json.dumps(
                    {
                        **_base(),
                        "scalars": {"k_Z2Sigma": 1},
                        "scalar_provenance": {
                            "k_Z2Sigma": "active_closed_projective_branch"
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
            curvature.write_text(json.dumps(_curvature_branch()), encoding="utf-8")
            charge.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "compressed_planck_lcdm_rd_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "observational_baryon_fit_used": False,
                        "normalizations": {
                            "projected_baryon_number_charge_Z2Sigma": 1.0e87
                        },
                        "normalization_provenance": {
                            "projected_baryon_number_charge_Z2Sigma": (
                                "active_projected_dirac_noether_charge_fixture"
                            )
                        },
                    }
                ),
                encoding="utf-8",
            )
            build_constants_payload(output_path=constants)
            temperature.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "direct_noncompressed_observation",
                        "compressed_planck_lcdm_rd_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "normalizations": {"photon_temperature0_Z2Sigma": 2.7255},
                        "normalization_provenance": {
                            "photon_temperature0_Z2Sigma": (
                                "FIRAS_direct_blackbody_temperature_input"
                            )
                        },
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                h0_input_path=h0,
                radius_input_path=radius,
                sign_input_path=sign,
                scale_input_path=scale,
                flrw_component_path=flrw,
                curvature_branch_path=curvature,
                charge_path=charge,
                constants_path=constants,
                temperature_path=temperature,
                omega_k_output_path=root / "omega.json",
                volume_input_path=root / "volume_input.json",
                volume_path=root / "volume.json",
                baryon_density_path=root / "n_b.json",
                saha_history_path=root / "saha.json",
                early_plasma_inputs_path=root / "early_plasma_inputs.json",
                early_plasma_manifest_path=root / "early_plasma.json",
                background_primitive_path=root / "background_primitive.json",
                plasma_primitive_path=root / "plasma_primitive.json",
                primitive_input_path=root / "primitive.json",
                scale_free_input_path=root / "scale_free.json",
            )

        self.assertTrue(payload["background_pipeline_passed"])
        self.assertTrue(payload["curvature_charge_saha_plasma_pipeline_passed"])
        self.assertTrue(payload["plasma_primitive_passed"])
        self.assertTrue(payload["split_primitives_chi2_passed"])
        self.assertTrue(payload["bao_chi2_evaluated"])
        self.assertTrue(payload["gate_passed"])
        self.assertIsNotNone(payload["chi2_DESI_DR2_BAO"])
        self.assertEqual(len(payload["prediction_vector"]), 13)
        self.assertFalse(payload["uses_compressed_planck_lcdm"])
        self.assertFalse(payload["uses_archived_z4"])


if __name__ == "__main__":
    unittest.main()
