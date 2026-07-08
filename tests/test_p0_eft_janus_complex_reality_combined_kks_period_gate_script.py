import unittest

from scripts.build_p0_eft_janus_complex_reality_combined_kks_period_gate import (
    build_payload,
)


class ComplexRealityCombinedKKSPeriodGateTests(unittest.TestCase):
    def test_symbolic_period_is_available(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["period_formula"], "Integral_CP1 Omega_j = 4*pi*j")
        self.assertTrue(payload["symbolic_combined_KKS_period_nonzero"])

    def test_janus_derived_period_is_not_available(self):
        payload = build_payload()

        self.assertFalse(payload["janus_derived_combined_KKS_period_nonzero"])
        self.assertFalse(payload["alpha_generated_now"])
        self.assertIn("sector_selection_law_derived", payload["still_missing"])


if __name__ == "__main__":
    unittest.main()
