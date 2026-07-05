import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate import (
    build_payload as build_constants_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_saha_ionization_history_gate import build_payload


class P0EFTJanusZ2SigmaSahaIonizationHistoryGateTests(unittest.TestCase):
    def test_blocks_without_required_active_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            payload = build_payload(
                baryon_input_path=base / "missing_baryon.json",
                temperature_input_path=base / "missing_temperature.json",
                constants_input_path=base / "missing_constants.json",
                output_path=base / "history.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "active_baryon_number_density_Z2Sigma")
        self.assertFalse(payload["baryon_input_valid"])
        self.assertFalse(payload["temperature_input_valid"])
        self.assertFalse(payload["codata_constants_valid"])
        self.assertIn("baryon_number_density", payload["upstream_frontiers"])
        self.assertIn("photon_temperature_firas", payload["upstream_frontiers"])
        self.assertIn("codata_constants", payload["upstream_frontiers"])
        self.assertIn(
            "baryon_number_density",
            payload["nearest_saha_history_frontier"]["blocks"],
        )
        self.assertFalse(payload["uses_compressed_planck_lcdm_rd"])
        self.assertFalse(payload["uses_archived_z4_inputs"])

    def test_writes_saha_history_from_active_fixture_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            baryon = base / "baryon.json"
            temperature = base / "temperature.json"
            constants = base / "constants.json"
            output = base / "history.json"
            baryon.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "compressed_planck_lcdm_rd_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "normalizations": {
                            "baryon_number_density0_m3_Z2Sigma": 1.0e9,
                        },
                        "normalization_provenance": {
                            "baryon_number_density0_m3_Z2Sigma": "test_noether_volume_fixture",
                        },
                    }
                ),
                encoding="utf-8",
            )
            temperature.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "direct_noncompressed_observation",
                        "compressed_planck_lcdm_rd_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "normalizations": {"photon_temperature0_Z2Sigma": 2.7255},
                    }
                ),
                encoding="utf-8",
            )
            build_constants_payload(output_path=constants)

            payload = build_payload(
                baryon_input_path=baryon,
                temperature_input_path=temperature,
                constants_input_path=constants,
                output_path=output,
            )
            self.assertTrue(output.exists())
            history = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(payload["nearest_saha_history_frontier"]["blocks"], [])
        self.assertEqual(history["ionization_model"], "hydrogen_saha_equilibrium")
        self.assertEqual(history["electrons_per_baryon"], 1.0)
        self.assertEqual(len(history["z_grid"]), len(history["ionization_fraction_Z2Sigma"]))
        self.assertGreater(history["ionization_fraction_Z2Sigma"][-1], history["ionization_fraction_Z2Sigma"][0])
        self.assertLessEqual(max(history["ionization_fraction_Z2Sigma"]), 1.0)
        self.assertFalse(history["compressed_planck_lcdm_rd_used"])
        self.assertFalse(history["archived_z4_reuse_used"])


if __name__ == "__main__":
    unittest.main()
