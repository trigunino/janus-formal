import unittest

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_pt_boundary_state_condition_gate import (
    build_payload,
)


class LLBranePTBoundaryStateConditionGateTests(unittest.TestCase):
    def test_pt_condition_fixes_sign_not_magnitude(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["closure"]["chi_LL_sign_fixed_negative"])
        self.assertTrue(payload["closure"]["chi_LL_constant_on_Sigma"])
        self.assertFalse(payload["closure"]["chi_LL_magnitude_fixed_by_PT_invariance"])
        self.assertFalse(payload["PT_boundary_state_selects_chi"])


if __name__ == "__main__":
    unittest.main()
