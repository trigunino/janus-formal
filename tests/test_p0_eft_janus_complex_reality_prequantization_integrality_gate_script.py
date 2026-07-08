import unittest

from scripts.build_p0_eft_janus_complex_reality_prequantization_integrality_gate import (
    build_payload,
)


class ComplexRealityPrequantizationIntegralityGateTests(unittest.TestCase):
    def test_prequantization_remains_blocked_without_closed_integral_cycle(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["prequantization_integrality_ready"])
        self.assertFalse(payload["alpha_generated_now"])
        self.assertEqual(payload["next_gate"], "ComplexRealityAlphaStateLawVerdictGate")
        self.assertIn("integral_over_2pi_hbar_is_integer", payload["still_missing"])
        self.assertIn("alpha_map_to_boundary_charge_derived", payload["still_missing"])


if __name__ == "__main__":
    unittest.main()
