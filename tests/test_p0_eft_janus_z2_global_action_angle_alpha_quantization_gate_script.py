import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_global_action_angle_alpha_quantization_gate import (
    HBAR_J_S,
    alpha_from_action_integral,
    build_payload,
)


class GlobalActionAngleAlphaQuantizationGateTests(unittest.TestCase):
    def test_live_action_angle_route_is_blocked_without_action_integral(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["action_angle_alpha_quantized"])
        self.assertIn("canonical_pair_qp_derived", payload["blocked_by"])
        self.assertIn("action_integral_I_alpha_derived", payload["blocked_by"])

    def test_formula_alpha_n_from_power_law_action_integral(self):
        alpha = alpha_from_action_integral(
            action_prefactor_SI=2.0 * math.pi * HBAR_J_S,
            alpha_power=1.0,
            integer_n=3,
        )

        self.assertAlmostEqual(alpha, 3.0)

    def test_complete_inputs_write_scale_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            inp = root / "inputs.json"
            out = root / "scale.json"
            inp.write_text(
                json.dumps(
                    {
                        "global_PT_cycle_identified": True,
                        "cycle_is_compact_closed": True,
                        "canonical_pair_qp_derived": True,
                        "symplectic_one_form_theta_derived": True,
                        "action_integral_I_alpha_derived": True,
                        "action_prefactor_SI": 2.0 * math.pi * HBAR_J_S,
                        "alpha_power": 1.0,
                        "bohr_sommerfeld_law_accepted": True,
                        "integer_n": 2,
                        "primitive_sector_selected": True,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=inp, output_path=out, write_output=True)
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["action_angle_alpha_quantized"])
        self.assertAlmostEqual(written["alpha_seconds"], 2.0)
        self.assertEqual(written["scale_provenance"], "global_action_angle_quantization")


if __name__ == "__main__":
    unittest.main()
