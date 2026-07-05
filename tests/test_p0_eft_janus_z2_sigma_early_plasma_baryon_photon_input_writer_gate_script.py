import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_baryon_photon_input_writer_gate import (
    build_payload,
)


def _payload(rho_baryon0=2.0, provenance="active_baryon_density_gate") -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": [10.0, 100.0, 1000.0],
        "normalizations": {
            "rho_baryon0_Z2Sigma": rho_baryon0,
            "photon_temperature0_Z2Sigma": 3.0,
            "radiation_constant_J_m3_K4": 4.0,
            "baryon_mass_kg": 2.0,
            "baryon_number_density0_m3_Z2Sigma": 1.0,
        },
        "normalization_provenance": {
            "rho_baryon0_Z2Sigma": provenance,
            "photon_temperature0_Z2Sigma": "active_temperature_gate",
            "radiation_constant_J_m3_K4": "active_radiation_constant_convention",
            "baryon_mass_kg": "active_baryon_mass_convention",
            "baryon_number_density0_m3_Z2Sigma": "active_baryon_number_gate",
        },
    }


class P0EFTJanusZ2SigmaEarlyPlasmaBaryonPhotonInputWriterGateTests(unittest.TestCase):
    def test_missing_input_blocks_writer(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                output_path=Path(tmp) / "baryon_photon.json",
            )
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["baryon_photon_input_written"])

    def test_valid_active_input_writes_baryon_photon_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "normalization.json"
            output_path = Path(tmp) / "baryon_photon.json"
            input_path.write_text(json.dumps(_payload()), encoding="utf-8")
            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))
        self.assertTrue(payload["gate_passed"])
        self.assertIn("rho_baryon0_Z2Sigma", written["normalizations"])
        self.assertFalse(written["archived_z4_reuse_used"])

    def test_density_mismatch_blocks_writer(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "normalization.json"
            output_path = Path(tmp) / "baryon_photon.json"
            input_path.write_text(json.dumps(_payload(rho_baryon0=3.0)), encoding="utf-8")
            payload = build_payload(input_path=input_path, output_path=output_path)
        self.assertFalse(payload["gate_passed"])
        self.assertIn("n_b0*baryon_mass", payload["validation_error"])

    def test_forbidden_provenance_blocks_writer(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "normalization.json"
            output_path = Path(tmp) / "baryon_photon.json"
            input_path.write_text(json.dumps(_payload(provenance="Planck LCDM")), encoding="utf-8")
            payload = build_payload(input_path=input_path, output_path=output_path)
        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
