import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_curvature_charge_to_saha_early_plasma_pipeline_gate import (
    build_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate import (
    build_payload as build_constants_payload,
)


def _curvature_branch() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {
            "H0_Z2Sigma_km_s_Mpc": 70.0,
            "R_curv_Z2Sigma_Mpc": 1000.0,
            "k_Z2Sigma": 1,
        },
        "scalar_provenance": {
            "H0_Z2Sigma": "active_background_scale_gate",
            "R_curv_Z2Sigma": "active_embedding_radius_gate",
            "k_Z2Sigma": "active_closed_projective_branch",
        },
        "spatial_topology": {"quotient_spatial_slice": "RP3"},
    }


class CurvatureChargeToSahaEarlyPlasmaPipelineGateTests(unittest.TestCase):
    def test_missing_inputs_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            payload = build_payload(
                curvature_branch_path=base / "missing_curvature.json",
                charge_path=base / "missing_charge.json",
                volume_input_path=base / "volume_input.json",
                volume_path=base / "volume.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["spatial_volume_input_passed"])
        self.assertIn("curvature_branch", payload["upstream_frontiers"])
        self.assertIn("projected_baryon_charge", payload["upstream_frontiers"])
        self.assertIn("spatial_volume_input", payload["upstream_frontiers"])
        self.assertIsNotNone(
            payload["upstream_frontiers"]["spatial_volume_input"]["nearest_frontier"]
        )
        self.assertIn(
            "active_R_curv_Z2Sigma_Mpc_from_embedding_or_throat_scale",
            payload["upstream_frontiers"]["spatial_volume_input"]["nearest_frontier"][
                "blocks"
            ],
        )
        self.assertIn("baryon_density_to_plasma", payload["upstream_frontiers"])
        self.assertIn(
            "dirac_charge_boundary_projection",
            payload["upstream_frontiers"]["projected_baryon_charge"]["upstream_frontiers"],
        )
        self.assertIn(
            "baryon_density",
            payload["upstream_frontiers"]["baryon_density_to_plasma"]["upstream_frontiers"],
        )
        self.assertTrue(payload["nearest_curvature_charge_plasma_frontier"]["diagnostic_only"])

    def test_curvature_and_charge_fixture_runs_to_early_plasma(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            curvature = base / "curvature.json"
            charge = base / "charge.json"
            constants = base / "constants.json"
            temperature = base / "temperature.json"
            early_plasma = base / "early_plasma.json"
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
                            "photon_temperature0_Z2Sigma": "FIRAS_direct_blackbody_temperature_input"
                        },
                    }
                ),
                encoding="utf-8",
            )
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
                        "normalizations": {"projected_baryon_number_charge_Z2Sigma": 1.0e87},
                        "normalization_provenance": {
                            "projected_baryon_number_charge_Z2Sigma": "test_projected_noether_charge"
                        },
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                curvature_branch_path=curvature,
                charge_path=charge,
                constants_path=constants,
                temperature_path=temperature,
                volume_input_path=base / "volume_input.json",
                volume_path=base / "volume.json",
                baryon_density_path=base / "n_b.json",
                saha_history_path=base / "saha.json",
                early_plasma_inputs_path=base / "early_plasma_inputs.json",
                early_plasma_manifest_path=early_plasma,
            )
            early_plasma_exists = early_plasma.exists()

        self.assertTrue(payload["gate_passed"])
        self.assertIn("projected_baryon_charge", payload["upstream_frontiers"])
        self.assertTrue(payload["spatial_volume_input_passed"])
        self.assertTrue(payload["spatial_volume_passed"])
        self.assertTrue(payload["noether_volume_to_saha_early_plasma_passed"])
        self.assertTrue(early_plasma_exists)


if __name__ == "__main__":
    unittest.main()
