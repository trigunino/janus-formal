import unittest

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_flux_quantization_gate import (
    build_payload,
)


class LLBraneFluxQuantizationGateTests(unittest.TestCase):
    def test_flux_quantization_is_formulated_but_not_closing(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["closure"]["aroundSigma_cycle_available"])
        self.assertTrue(payload["closure"]["integer_flux_condition_formulated"])
        self.assertFalse(payload["closure"]["chi_LL_flux_relation_derived"])
        self.assertFalse(payload["flux_quantization_selects_chi"])


if __name__ == "__main__":
    unittest.main()
