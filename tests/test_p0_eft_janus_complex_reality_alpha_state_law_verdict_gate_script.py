import unittest

from scripts.build_p0_eft_janus_complex_reality_alpha_state_law_verdict_gate import (
    build_payload,
)


class ComplexRealityAlphaStateLawVerdictGateTests(unittest.TestCase):
    def test_alpha_state_law_is_not_generated(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["alpha_prediction_ready"])
        self.assertFalse(payload["alpha_generated_now"])
        self.assertEqual(payload["branch_status"], "frozen_pending_state_law")
        self.assertIn("prequantization_integral_ready", payload["still_missing"])
        self.assertIn("global_alpha_map_derived", payload["still_missing"])


if __name__ == "__main__":
    unittest.main()
