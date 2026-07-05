import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_ionization_thomson_input_writer_gate import (
    build_payload,
)


def _payload(provenance="active_ionization_gate") -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": [10.0, 100.0, 1000.0],
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


class P0EFTJanusZ2SigmaEarlyPlasmaIonizationThomsonInputWriterGateTests(unittest.TestCase):
    def test_missing_input_blocks_writer(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                output_path=Path(tmp) / "ionization_thomson.json",
        )
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "active_ionization_thomson_normalization_inputs")
        self.assertFalse(payload["ionization_thomson_input_written"])

    def test_valid_active_input_writes_ionization_thomson_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "normalization.json"
            output_path = Path(tmp) / "ionization_thomson.json"
            input_path.write_text(json.dumps(_payload()), encoding="utf-8")
            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertIn("sigma_thomson_m2", written["normalizations"])
        self.assertFalse(written["compressed_planck_lcdm_rd_used"])

    def test_forbidden_provenance_blocks_writer(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "normalization.json"
            output_path = Path(tmp) / "ionization_thomson.json"
            input_path.write_text(json.dumps(_payload(provenance="archived Z4")), encoding="utf-8")
            payload = build_payload(input_path=input_path, output_path=output_path)
        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
