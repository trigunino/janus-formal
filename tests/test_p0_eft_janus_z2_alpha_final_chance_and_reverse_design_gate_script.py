import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_alpha_final_chance_and_reverse_design_gate import (
    build_payload,
    required_charge_unit_for_alpha,
    required_mass_for_alpha,
)


class AlphaFinalChanceAndReverseDesignGateTests(unittest.TestCase):
    def test_live_gate_closes_with_no_internal_alpha_derivation(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["direct_internal_alpha_derivation_available"])
        self.assertEqual(payload["best_honest_current_use"], "alpha_as_explicit_state_sector")
        self.assertEqual(len(payload["direct_routes"]), 4)

    def test_target_alpha_yields_required_mass_and_charge_unit(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(
                json.dumps(
                    {
                        "published_alpha_m": 2.0,
                        "c_m_s": 3.0,
                        "G_SI": 5.0,
                        "integer_n": 2,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(path)

        self.assertTrue(payload["target_alpha_matching"]["target_alpha_available"])
        self.assertAlmostEqual(
            payload["target_alpha_matching"]["required_boundary_mass_kg"],
            18.0 / (10.0 * math.pi),
        )
        self.assertAlmostEqual(
            payload["target_alpha_matching"]["required_charge_unit_kg_for_n"],
            9.0 / (10.0 * math.pi),
        )

    def test_formula_helpers_reject_invalid_inputs(self):
        with self.assertRaises(ValueError):
            required_mass_for_alpha(0.0, 3.0, 5.0)
        with self.assertRaises(ValueError):
            required_charge_unit_for_alpha(alpha_m=1.0, integer_n=0, c_m_s=3.0, g_si=5.0)


if __name__ == "__main__":
    unittest.main()
