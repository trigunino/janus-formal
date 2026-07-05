import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_physical_input_obligation_gate import (
    build_payload,
)


def _baryon_photon_inputs() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": [100.0, 1000.0, 10000.0],
        "normalizations": {
            "rho_baryon0_Z2Sigma": 2.0,
            "photon_temperature0_Z2Sigma": 3.0,
            "radiation_constant_J_m3_K4": 4.0,
            "baryon_mass_kg": 2.0,
            "baryon_number_density0_m3_Z2Sigma": 1.0,
        },
        "normalization_provenance": {
            "rho_baryon0_Z2Sigma": "active_baryon_density_gate",
            "photon_temperature0_Z2Sigma": "active_temperature_gate",
            "radiation_constant_J_m3_K4": "explicit_radiation_constant_convention",
            "baryon_mass_kg": "explicit_baryon_mass_convention",
            "baryon_number_density0_m3_Z2Sigma": "active_baryon_number_gate",
        },
    }


def _ionization_thomson_inputs() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": [100.0, 1000.0, 10000.0],
        "normalizations": {
            "ionization_fraction_Z2Sigma": 0.5,
            "electrons_per_baryon": 0.8,
            "sigma_thomson_m2": 1.0e-40,
        },
        "normalization_provenance": {
            "ionization_fraction_Z2Sigma": "active_ionization_gate",
            "electrons_per_baryon": "active_charge_convention",
            "sigma_thomson_m2": "explicit_thomson_cross_section_convention",
        },
    }


class P0EFTJanusZ2SigmaEarlyPlasmaPhysicalInputObligationGateTests(unittest.TestCase):
    def test_missing_inputs_block_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                baryon_photon_input_path=root / "missing_baryon_photon.json",
                ionization_thomson_input_path=root / "missing_ionization.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["early_plasma_physical_inputs_ready"])
        self.assertIn(
            "early_plasma_baryon_photon_normalization_inputs",
            payload["missing_physical_inputs"],
        )
        self.assertIn(
            "early_plasma_ionization_thomson_normalization_inputs",
            payload["missing_physical_inputs"],
        )

    def test_valid_inputs_enable_early_plasma_builders(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            baryon = root / "baryon_photon.json"
            ionization = root / "ionization.json"
            baryon.write_text(json.dumps(_baryon_photon_inputs()), encoding="utf-8")
            ionization.write_text(json.dumps(_ionization_thomson_inputs()), encoding="utf-8")

            payload = build_payload(
                baryon_photon_input_path=baryon,
                ionization_thomson_input_path=ionization,
            )

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["builders_ready_after_inputs"]["c_s_over_c_Z2Sigma"])
        self.assertTrue(payload["builders_ready_after_inputs"]["Gamma_drag_Z2Sigma"])
        self.assertTrue(payload["requires_background_H0_for_Gamma_over_H0"])
        self.assertTrue(payload["requires_active_E_Z2Sigma_for_z_d_solver"])


if __name__ == "__main__":
    unittest.main()
