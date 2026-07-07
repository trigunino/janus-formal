import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_global_souriau_orbit_quantization_gate import (
    build_payload,
)


class GlobalSouriauOrbitQuantizationGateTests(unittest.TestCase):
    def test_live_global_orbit_is_continuous_not_quantized(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["global_orbit_quantized"])
        self.assertIn("mass_orbit_lattice_derived", payload["blocked_by"])

    def test_quantized_global_orbit_writes_composite_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            inp = root / "inputs.json"
            out = root / "composite.json"
            inp.write_text(
                json.dumps(
                    {
                        "global_state_space_declared": True,
                        "geometric_quantization_performed": True,
                        "integrality_condition_on_global_orbit": True,
                        "mass_orbit_lattice_derived": True,
                        "minimal_mass_unit_kg": 2.0,
                        "primitive_sector_n": 1,
                        "primitive_sector_selected": True,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=inp, output_path=out, write_output=True)
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["global_orbit_quantized"])
        self.assertEqual(written["charge_unit_kg"], 2.0)
        self.assertEqual(written["integer_sector_n"], 1)


if __name__ == "__main__":
    unittest.main()
