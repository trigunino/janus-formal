import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_background_gravity_codata_convention_gate import (
    G_CODATA_2022_SI,
    build_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_gravity_input_writer_gate import (
    build_payload as build_gravity_writer_payload,
)


class P0EFTJanusZ2SigmaBackgroundGravityCODATAConventionGateTests(unittest.TestCase):
    def test_writes_active_gravity_convention_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "background_gravity_normalization_inputs.json"
            payload = build_payload(output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["output_written"])
        self.assertEqual(
            written["scalars"]["gravitational_constant_si_Z2Sigma"],
            G_CODATA_2022_SI,
        )
        self.assertFalse(written["compressed_planck_lcdm_background_used"])
        self.assertIn("NIST_CODATA_2022", written["scalar_provenance"]["G_Z2Sigma"])

    def test_existing_gravity_writer_accepts_convention_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            convention = root / "background_gravity_normalization_inputs.json"
            out = root / "background_gravity_inputs.json"
            build_payload(output_path=convention)
            payload = build_gravity_writer_payload(input_path=convention, output_path=out)
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(
            written["scalars"]["gravitational_constant_si_Z2Sigma"],
            G_CODATA_2022_SI,
        )
        self.assertEqual(written["source"], "active_derived")


if __name__ == "__main__":
    unittest.main()
