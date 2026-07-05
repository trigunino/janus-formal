import json
import tempfile
import unittest
from pathlib import Path

from janus_lab.z2_sigma_early_plasma_inputs import load_active_z2sigma_early_plasma_input_manifest
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate import (
    build_payload as build_constants_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_saha_inputs_assembler_gate import (
    build_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_saha_ionization_history_gate import (
    build_payload as build_saha_payload,
)


class EarlyPlasmaSahaInputsAssemblerGateTests(unittest.TestCase):
    def test_missing_inputs_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            payload = build_payload(
                constants_path=base / "missing_constants.json",
                temperature_path=base / "missing_temperature.json",
                saha_history_path=base / "missing_saha.json",
                output_path=base / "early_plasma_inputs.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["constants_valid"])
        self.assertFalse(payload["temperature_valid"])
        self.assertFalse(payload["saha_history_valid"])

    def test_valid_saha_history_writes_early_plasma_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            constants = base / "constants.json"
            temperature = base / "temperature.json"
            baryon = base / "baryon.json"
            saha = base / "saha.json"
            output = base / "early_plasma_inputs.json"
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
                            "baryon_number_density0_m3_Z2Sigma_provenance": "test_active_fixture",
                        },
                    }
                ),
                encoding="utf-8",
            )
            build_saha_payload(
                baryon_input_path=baryon,
                temperature_input_path=temperature,
                constants_input_path=constants,
                output_path=saha,
            )

            payload = build_payload(
                constants_path=constants,
                temperature_path=temperature,
                saha_history_path=saha,
                output_path=output,
            )
            manifest = load_active_z2sigma_early_plasma_input_manifest(output)

        self.assertTrue(payload["gate_passed"])
        self.assertIn("ionization_history", manifest)
        self.assertNotIn("ionization_fraction_Z2Sigma", manifest["normalizations"])
        self.assertFalse(manifest["compressed_planck_lcdm_rd_used"])
        self.assertFalse(manifest["archived_z4_reuse_used"])


if __name__ == "__main__":
    unittest.main()
