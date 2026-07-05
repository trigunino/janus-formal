import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate import (
    build_payload as build_constants_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_model_normalization_assembler_gate import (
    build_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_temperature_firas_gate import (
    T_CMB_FIRAS_K,
    build_payload as build_temperature_payload,
)


def _model_payload(baryon_mass: float) -> dict:
    n_b = 3.0
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": [10.0, 100.0, 1000.0],
        "normalizations": {
            "baryon_number_density0_m3_Z2Sigma": n_b,
            "ionization_fraction_Z2Sigma": 0.4,
            "electrons_per_baryon": 0.8,
        },
        "normalization_provenance": {
            "baryon_number_density0_m3_Z2Sigma": "active_number_derivation",
            "ionization_fraction_Z2Sigma": "active_ionization_derivation",
            "electrons_per_baryon": "active_composition_derivation",
        },
    }


class P0EFTJanusZ2SigmaEarlyPlasmaModelNormalizationAssemblerGateTests(unittest.TestCase):
    def test_missing_model_manifest_blocks_assembler(self):
        with tempfile.TemporaryDirectory() as tmp:
            constants = Path(tmp) / "constants.json"
            temperature = Path(tmp) / "temperature.json"
            build_constants_payload(output_path=constants)
            build_temperature_payload(output_path=temperature)
            payload = build_payload(
                constants_path=constants,
                temperature_path=temperature,
                model_input_path=Path(tmp) / "missing.json",
                baryon_photon_output_path=Path(tmp) / "bp.json",
                ionization_thomson_output_path=Path(tmp) / "it.json",
            )
        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["constants_manifest_exists"])
        self.assertFalse(payload["model_input_manifest_exists"])
        self.assertEqual(payload["primary_blocker"], "active_early_plasma_model_normalizations")

    def test_combines_codata_constants_with_model_normalizations(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            constants = root / "constants.json"
            temperature = root / "temperature.json"
            build_constants_payload(output_path=constants)
            build_temperature_payload(output_path=temperature)
            constants_payload = json.loads(constants.read_text(encoding="utf-8"))
            model = root / "model.json"
            model.write_text(
                json.dumps(_model_payload(constants_payload["constants"]["baryon_mass_kg"])),
                encoding="utf-8",
            )
            bp = root / "bp.json"
            it = root / "it.json"
            payload = build_payload(
                constants_path=constants,
                temperature_path=temperature,
                model_input_path=model,
                baryon_photon_output_path=bp,
                ionization_thomson_output_path=it,
            )
            bp_payload = json.loads(bp.read_text(encoding="utf-8"))
            it_payload = json.loads(it.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertIn("radiation_constant_J_m3_K4", bp_payload["normalizations"])
        self.assertAlmostEqual(
            bp_payload["normalizations"]["rho_baryon0_Z2Sigma"],
            3.0 * constants_payload["constants"]["baryon_mass_kg"],
        )
        self.assertEqual(
            bp_payload["normalizations"]["photon_temperature0_Z2Sigma"],
            T_CMB_FIRAS_K,
        )
        self.assertIn("sigma_thomson_m2", it_payload["normalizations"])
        self.assertFalse(bp_payload["archived_z4_reuse_used"])
        self.assertFalse(it_payload["compressed_planck_lcdm_rd_used"])


if __name__ == "__main__":
    unittest.main()
