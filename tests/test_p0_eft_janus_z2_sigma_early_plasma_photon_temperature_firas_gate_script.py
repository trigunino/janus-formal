import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_temperature_firas_gate import (
    T_CMB_FIRAS_K,
    build_payload,
)


class P0EFTJanusZ2SigmaEarlyPlasmaPhotonTemperatureFIRASGateTests(unittest.TestCase):
    def test_writes_direct_noncompressed_temperature_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "temperature.json"
            payload = build_payload(output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(
            written["normalizations"]["photon_temperature0_Z2Sigma"],
            T_CMB_FIRAS_K,
        )
        self.assertEqual(written["source"], "direct_noncompressed_observation")
        self.assertFalse(written["compressed_planck_lcdm_rd_used"])
        self.assertFalse(written["archived_z4_reuse_used"])
        self.assertTrue(payload["does_not_fix_baryon_or_ionization_normalizations"])

    def test_existing_output_can_be_validated_without_rewrite(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "temperature.json"
            build_payload(output_path=output)
            payload = build_payload(output_path=output, write_output=False)

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["output_written"])


if __name__ == "__main__":
    unittest.main()
