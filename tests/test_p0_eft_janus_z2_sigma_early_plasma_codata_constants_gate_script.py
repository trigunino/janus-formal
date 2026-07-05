import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate import (
    RADIATION_CONSTANT_SI,
    HYDROGEN_IONIZATION_ENERGY_NIST_J,
    THOMSON_CROSS_SECTION_2022_M2,
    build_payload,
)


class P0EFTJanusZ2SigmaEarlyPlasmaCODATAConstantsGateTests(unittest.TestCase):
    def test_writes_codata_constants_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "constants.json"
            payload = build_payload(output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(
            written["constants"]["radiation_constant_J_m3_K4"],
            RADIATION_CONSTANT_SI,
        )
        self.assertEqual(
            written["constants"]["sigma_thomson_m2"],
            THOMSON_CROSS_SECTION_2022_M2,
        )
        self.assertEqual(
            written["constants"]["hydrogen_ionization_energy_J"],
            HYDROGEN_IONIZATION_ENERGY_NIST_J,
        )
        self.assertIn("electron_mass_kg", written["constants"])
        self.assertIn("boltzmann_constant_J_K", written["constants"])
        self.assertIn("hbar_J_s", written["constants"])
        self.assertTrue(payload["does_not_fix_model_normalizations"])
        self.assertIn("rho_baryon0_Z2Sigma", payload["still_required_model_inputs"])

    def test_existing_output_can_be_validated_without_rewrite(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "constants.json"
            build_payload(output_path=output)
            payload = build_payload(output_path=output, write_output=False)

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["output_written"])


if __name__ == "__main__":
    unittest.main()
