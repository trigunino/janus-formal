import json
import tempfile
import unittest
from pathlib import Path

from janus_lab.z2_sigma_early_plasma_inputs import (
    assemble_active_z2sigma_early_plasma_input_manifest,
    build_active_z2sigma_ionization_thomson_input_payload,
    load_active_z2sigma_early_plasma_input_manifest,
)


def _payload() -> dict:
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


class Z2SigmaEarlyPlasmaInputManifestTests(unittest.TestCase):
    def test_loader_accepts_strict_active_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(_payload()), encoding="utf-8")

            payload = load_active_z2sigma_early_plasma_input_manifest(path)

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["normalizations"]["rho_baryon0_Z2Sigma"], 2.0)

    def test_loader_accepts_active_ionization_history(self):
        payload = _payload()
        payload["normalizations"].pop("ionization_fraction_Z2Sigma")
        payload["normalization_provenance"].pop("ionization_fraction_Z2Sigma")
        payload["ionization_history"] = {
            "z_grid": payload["z_grid"],
            "ionization_fraction_Z2Sigma": [0.1, 0.5, 0.9],
            "provenance": "active_saha_ionization_history_gate",
        }
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(payload), encoding="utf-8")

            loaded = load_active_z2sigma_early_plasma_input_manifest(path)

        self.assertEqual(
            loaded["ionization_history"]["provenance"],
            "active_saha_ionization_history_gate",
        )

    def test_partial_ionization_payload_accepts_history(self):
        payload = _payload()
        payload["normalizations"] = {
            "electrons_per_baryon": 0.8,
            "sigma_thomson_m2": 6.6524587321e-29,
        }
        payload["normalization_provenance"] = {
            "electrons_per_baryon": "active_charge_convention",
            "sigma_thomson_m2": "explicit_thomson_cross_section_convention",
        }
        payload["ionization_history"] = {
            "z_grid": payload["z_grid"],
            "ionization_fraction_Z2Sigma": [0.1, 0.5, 0.9],
            "provenance": "active_saha_ionization_history_gate",
        }

        built = build_active_z2sigma_ionization_thomson_input_payload(payload)

        self.assertIn("ionization_history", built)
        self.assertNotIn("ionization_fraction_Z2Sigma", built["normalizations"])

    def test_assembler_preserves_ionization_history(self):
        baryon_photon = _payload()
        for key in ["ionization_fraction_Z2Sigma", "electrons_per_baryon", "sigma_thomson_m2"]:
            baryon_photon["normalizations"].pop(key)
            baryon_photon["normalization_provenance"].pop(key)
        ionization = _payload()
        ionization["normalizations"] = {
            "electrons_per_baryon": 0.8,
            "sigma_thomson_m2": 6.6524587321e-29,
        }
        ionization["normalization_provenance"] = {
            "electrons_per_baryon": "active_charge_convention",
            "sigma_thomson_m2": "explicit_thomson_cross_section_convention",
        }
        ionization["ionization_history"] = {
            "z_grid": ionization["z_grid"],
            "ionization_fraction_Z2Sigma": [0.1, 0.5, 0.9],
            "provenance": "active_saha_ionization_history_gate",
        }

        manifest = assemble_active_z2sigma_early_plasma_input_manifest(
            baryon_photon_payload=baryon_photon,
            ionization_thomson_payload=build_active_z2sigma_ionization_thomson_input_payload(
                ionization
            ),
        )

        self.assertIn("ionization_history", manifest)
        self.assertNotIn("ionization_fraction_Z2Sigma", manifest["normalizations"])

    def test_loader_rejects_forbidden_provenance(self):
        payload = _payload()
        payload["normalization_provenance"]["photon_temperature0_Z2Sigma"] = "Planck LCDM"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(payload), encoding="utf-8")

            with self.assertRaises(ValueError):
                load_active_z2sigma_early_plasma_input_manifest(path)

    def test_loader_rejects_inconsistent_baryon_density(self):
        payload = _payload()
        payload["normalizations"]["rho_baryon0_Z2Sigma"] = 3.0
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(payload), encoding="utf-8")

            with self.assertRaises(ValueError):
                load_active_z2sigma_early_plasma_input_manifest(path)


if __name__ == "__main__":
    unittest.main()
