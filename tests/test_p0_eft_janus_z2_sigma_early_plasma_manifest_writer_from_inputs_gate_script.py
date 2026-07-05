import json
import tempfile
import unittest
from pathlib import Path

from janus_lab.z2_sigma_early_plasma_manifest import load_active_z2sigma_early_plasma_manifest
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_manifest_writer_from_inputs_gate import (
    build_payload,
)


def _input_payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": [10.0, 100.0, 1000.0],
        "normalizations": {
            "rho_baryon0_Z2Sigma": 2.0,
            "photon_temperature0_Z2Sigma": 3.0,
            "radiation_constant_J_m3_K4": 4.0,
            "baryon_mass_kg": 2.0,
            "baryon_number_density0_m3_Z2Sigma": 1.0,
            "ionization_fraction_Z2Sigma": 0.5,
            "electrons_per_baryon": 0.8,
            "sigma_thomson_m2": 6.6524587321e-29,
        },
        "normalization_provenance": {
            "rho_baryon0_Z2Sigma": "active_baryon_density_gate",
            "photon_temperature0_Z2Sigma": "active_temperature_gate",
            "radiation_constant_J_m3_K4": "explicit_radiation_constant_convention",
            "baryon_mass_kg": "explicit_baryon_mass_convention",
            "baryon_number_density0_m3_Z2Sigma": "active_baryon_number_gate",
            "ionization_fraction_Z2Sigma": "active_ionization_gate",
            "electrons_per_baryon": "active_charge_convention",
            "sigma_thomson_m2": "explicit_thomson_cross_section_convention",
        },
    }


class P0EFTJanusZ2SigmaEarlyPlasmaManifestWriterFromInputsGateTests(unittest.TestCase):
    def test_missing_input_blocks_manifest_write(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                manifest_path=Path(tmp) / "early_plasma.json",
            )

        self.assertFalse(payload["input_exists"])
        self.assertFalse(payload["manifest_written"])
        self.assertFalse(payload["gate_passed"])

    def test_valid_active_inputs_write_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "early_plasma_inputs.json"
            output_path = tmpdir / "early_plasma.json"
            input_path.write_text(json.dumps(_input_payload()), encoding="utf-8")

            payload = build_payload(input_path=input_path, manifest_path=output_path)
            manifest = load_active_z2sigma_early_plasma_manifest(output_path)

        self.assertTrue(payload["input_valid"])
        self.assertTrue(payload["manifest_written"])
        self.assertTrue(payload["gate_passed"])
        self.assertIn("rho_baryon_Z2Sigma", manifest["early_plasma"])
        self.assertFalse(manifest["compressed_planck_lcdm_rd_used"])

    def test_valid_active_ionization_history_writes_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "early_plasma_inputs.json"
            output_path = tmpdir / "early_plasma.json"
            payload = _input_payload()
            payload["normalizations"].pop("ionization_fraction_Z2Sigma")
            payload["normalization_provenance"].pop("ionization_fraction_Z2Sigma")
            payload["ionization_history"] = {
                "z_grid": payload["z_grid"],
                "ionization_fraction_Z2Sigma": [0.1, 0.5, 0.9],
                "provenance": "active_saha_ionization_history_gate",
            }
            input_path.write_text(json.dumps(payload), encoding="utf-8")

            result = build_payload(input_path=input_path, manifest_path=output_path)
            manifest = load_active_z2sigma_early_plasma_manifest(output_path)

        self.assertTrue(result["gate_passed"])
        self.assertIn("Gamma_drag_Z2Sigma", manifest["early_plasma"])
        self.assertGreater(
            manifest["early_plasma"]["Gamma_drag_Z2Sigma"][-1],
            manifest["early_plasma"]["Gamma_drag_Z2Sigma"][0],
        )


if __name__ == "__main__":
    unittest.main()
