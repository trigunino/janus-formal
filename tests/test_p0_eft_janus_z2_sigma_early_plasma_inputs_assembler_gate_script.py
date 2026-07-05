import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_inputs_assembler_gate import (
    build_payload,
)


def _baryon_photon_payload(rho_baryon0=2.0, z_grid=None) -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": z_grid or [10.0, 100.0, 1000.0],
        "normalizations": {
            "rho_baryon0_Z2Sigma": rho_baryon0,
            "photon_temperature0_Z2Sigma": 3.0,
            "radiation_constant_J_m3_K4": 4.0,
            "baryon_mass_kg": 2.0,
            "baryon_number_density0_m3_Z2Sigma": 1.0,
        },
        "normalization_provenance": {
            "rho_baryon0_Z2Sigma": "active_baryon_density_gate",
            "photon_temperature0_Z2Sigma": "active_temperature_gate",
            "radiation_constant_J_m3_K4": "active_radiation_constant_convention",
            "baryon_mass_kg": "active_baryon_mass_convention",
            "baryon_number_density0_m3_Z2Sigma": "active_baryon_number_gate",
        },
    }


def _ionization_thomson_payload(z_grid=None, provenance="active_ionization_gate") -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": z_grid or [10.0, 100.0, 1000.0],
        "normalizations": {
            "ionization_fraction_Z2Sigma": 0.5,
            "electrons_per_baryon": 0.8,
            "sigma_thomson_m2": 6.6524587321e-29,
        },
        "normalization_provenance": {
            "ionization_fraction_Z2Sigma": provenance,
            "electrons_per_baryon": "active_charge_convention",
            "sigma_thomson_m2": "active_thomson_cross_section_convention",
        },
    }


class P0EFTJanusZ2SigmaEarlyPlasmaInputsAssemblerGateTests(unittest.TestCase):
    def test_missing_input_manifests_block_assembler(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                baryon_photon_path=Path(tmp) / "missing_baryon.json",
                ionization_thomson_path=Path(tmp) / "missing_ionization.json",
                output_path=Path(tmp) / "early_plasma_inputs.json",
            )

        self.assertFalse(payload["early_plasma_inputs_written"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "baryon_photon_and_ionization_thomson_inputs")

    def test_active_input_manifests_write_early_plasma_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            baryon = tmpdir / "baryon.json"
            ionization = tmpdir / "ionization.json"
            output = tmpdir / "early_plasma_inputs.json"
            baryon.write_text(json.dumps(_baryon_photon_payload()), encoding="utf-8")
            ionization.write_text(json.dumps(_ionization_thomson_payload()), encoding="utf-8")

            payload = build_payload(
                baryon_photon_path=baryon,
                ionization_thomson_path=ionization,
                output_path=output,
            )
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(written["active_core"], "Z2_tunnel_Sigma")
        self.assertIn("rho_baryon0_Z2Sigma", written["normalizations"])
        self.assertIn("sigma_thomson_m2", written["normalizations"])
        self.assertFalse(written["compressed_planck_lcdm_rd_used"])

    def test_baryon_mass_density_mismatch_blocks_assembler(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            baryon = tmpdir / "baryon.json"
            ionization = tmpdir / "ionization.json"
            output = tmpdir / "early_plasma_inputs.json"
            baryon.write_text(
                json.dumps(_baryon_photon_payload(rho_baryon0=3.0)),
                encoding="utf-8",
            )
            ionization.write_text(json.dumps(_ionization_thomson_payload()), encoding="utf-8")

            payload = build_payload(
                baryon_photon_path=baryon,
                ionization_thomson_path=ionization,
                output_path=output,
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("n_b0*baryon_mass", payload["validation_error"])

    def test_forbidden_provenance_blocks_assembler(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            baryon = tmpdir / "baryon.json"
            ionization = tmpdir / "ionization.json"
            output = tmpdir / "early_plasma_inputs.json"
            baryon.write_text(json.dumps(_baryon_photon_payload()), encoding="utf-8")
            ionization.write_text(
                json.dumps(_ionization_thomson_payload(provenance="Planck LCDM fit")),
                encoding="utf-8",
            )

            payload = build_payload(
                baryon_photon_path=baryon,
                ionization_thomson_path=ionization,
                output_path=output,
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
