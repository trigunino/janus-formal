import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_temperature_firas_gate import (
    build_payload as build_temperature_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_saha_ionization_readiness_gate import (
    build_payload,
)


def _model_payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "normalizations": {
            "baryon_number_density0_m3_Z2Sigma": 1.0,
        },
        "normalization_provenance": {
            "baryon_number_density0_m3_Z2Sigma": "test_noether_volume_fixture",
        },
    }


class P0EFTJanusZ2SigmaSahaIonizationReadinessGateTests(unittest.TestCase):
    def test_missing_baryon_number_blocks_saha_values(self):
        with tempfile.TemporaryDirectory() as tmp:
            temperature = Path(tmp) / "temperature.json"
            build_temperature_payload(output_path=temperature)
            payload = build_payload(
                baryon_model_input_path=Path(tmp) / "missing.json",
                photon_temperature_path=temperature,
            )

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["temperature_input_valid"])
        self.assertFalse(payload["active_baryon_number_input_valid"])
        self.assertFalse(payload["uses_planck_lcdm_recombination_history"])

    def test_baryon_number_and_temperature_enable_saha_values(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            model = root / "model.json"
            temperature = root / "temperature.json"
            model.write_text(json.dumps(_model_payload()), encoding="utf-8")
            build_temperature_payload(output_path=temperature)
            payload = build_payload(
                baryon_model_input_path=model,
                photon_temperature_path=temperature,
            )

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["saha_equilibrium_formula_declared"])
        self.assertTrue(payload["saha_ionization_values_ready"])
        self.assertFalse(payload["full_peebles_recfast_history_ready"])


if __name__ == "__main__":
    unittest.main()
