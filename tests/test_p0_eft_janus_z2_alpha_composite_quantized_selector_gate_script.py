import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_alpha_composite_quantized_selector_gate import (
    alpha_from_quantized_mass_unit,
    build_payload,
)


class AlphaCompositeQuantizedSelectorGateTests(unittest.TestCase):
    def test_formula(self):
        self.assertAlmostEqual(
            alpha_from_quantized_mass_unit(2, 3.0, 5.0, 7.0),
            2.0 * math.pi * 5.0 * 2.0 * 3.0 / 49.0,
        )

    def test_live_gate_is_blocked_without_composite_inputs(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["alpha_spectrum_ready"])
        self.assertFalse(payload["unique_alpha_selector_ready"])

    def test_writes_state_sector_when_spectrum_is_ready(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            inp = root / "input.json"
            out = root / "state.json"
            inp.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "noether_or_souriau_charge_to_alpha_map_derived": True,
                        "charge_lattice_quantized": True,
                        "charge_unit_kg": 3.0,
                        "charge_unit_provenance": "pt_souriau_charge_unit",
                        "integer_sector_n": 2,
                        "primitive_sector_selected": False,
                        "primitive_sector_provenance": "not_selected",
                        "c_plus0_m_s": 7.0,
                        "c_minus0_m_s": 7.0,
                        "G_plus_SI": 5.0,
                        "observational_fit_used": False,
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=inp, output_path=out, write_output=True)
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["alpha_spectrum_ready"])
        self.assertFalse(payload["unique_alpha_selector_ready"])
        self.assertTrue(written["alpha_sector_declared_not_derived"])
        self.assertFalse(written["full_no_fit_prediction_ready"])


if __name__ == "__main__":
    unittest.main()
