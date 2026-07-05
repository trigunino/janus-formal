import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate import (
    build_payload as build_constants_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_noether_volume_to_saha_early_plasma_pipeline_gate import (
    build_payload,
)


class NoetherVolumeToSahaEarlyPlasmaPipelineGateTests(unittest.TestCase):
    def test_missing_charge_or_volume_blocks_pipeline(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            constants = base / "constants.json"
            temperature = base / "temperature.json"
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
            payload = build_payload(
                charge_path=base / "missing_charge.json",
                volume_path=base / "missing_volume.json",
                constants_path=constants,
                temperature_path=temperature,
                baryon_density_path=base / "n_b.json",
                saha_history_path=base / "saha.json",
                early_plasma_inputs_path=base / "early_plasma_inputs.json",
                early_plasma_manifest_path=base / "early_plasma.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["baryon_density_passed"])
        self.assertIn("baryon_density", payload["upstream_frontiers"])
        self.assertIn(
            "projected_baryon_charge",
            payload["upstream_frontiers"]["baryon_density"]["upstream_frontiers"],
        )
        self.assertIn(
            "spatial_volume",
            payload["upstream_frontiers"]["baryon_density"]["upstream_frontiers"],
        )
        self.assertIn(
            "projected_baryon_charge",
            payload["upstream_frontiers"]["baryon_density"]["nearest_frontier"][
                "blocks"
            ],
        )
        self.assertIn("saha_history", payload["upstream_frontiers"])
        self.assertIn(
            "baryon_number_density",
            payload["upstream_frontiers"]["saha_history"]["upstream_frontiers"],
        )
        self.assertIn(
            "baryon_number_density",
            payload["upstream_frontiers"]["saha_history"]["nearest_frontier"]["blocks"],
        )
        self.assertIn("saha_inputs", payload["upstream_frontiers"])
        self.assertIn("early_plasma_manifest", payload["upstream_frontiers"])
        self.assertTrue(payload["nearest_noether_volume_plasma_frontier"]["diagnostic_only"])

    def test_explicit_active_noether_volume_fixture_builds_plasma_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            charge = base / "charge.json"
            volume = base / "volume.json"
            constants = base / "constants.json"
            temperature = base / "temperature.json"
            early_plasma = base / "early_plasma.json"
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
                            "projected_baryon_number_charge_Z2Sigma": 1.0e87,
                        },
                        "normalization_provenance": {
                            "projected_baryon_number_charge_Z2Sigma": "test_projected_noether_charge",
                        },
                    }
                ),
                encoding="utf-8",
            )
            volume.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "compressed_planck_lcdm_rd_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "normalizations": {
                            "spatial_volume0_m3_Z2Sigma": 1.0e78,
                        },
                        "normalization_provenance": {
                            "spatial_volume0_m3_Z2Sigma": "test_active_projective_volume",
                        },
                        "volume_policy": {
                            "z2_cover_factor_applied_once": True,
                            "volume_convention": "test_projective_slice",
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
                            "photon_temperature0_Z2Sigma": "FIRAS_direct_blackbody_temperature_input"
                        },
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                charge_path=charge,
                volume_path=volume,
                constants_path=constants,
                temperature_path=temperature,
                baryon_density_path=base / "n_b.json",
                saha_history_path=base / "saha.json",
                early_plasma_inputs_path=base / "early_plasma_inputs.json",
                early_plasma_manifest_path=early_plasma,
            )
            early_plasma_exists = early_plasma.exists()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["baryon_density_passed"])
        self.assertTrue(payload["early_plasma_manifest_passed"])
        self.assertTrue(early_plasma_exists)


if __name__ == "__main__":
    unittest.main()
