import unittest

from scripts.build_p0_eft_janus_complex_reality_combined_branch_verdict_gate import (
    build_payload,
)


class ComplexRealityCombinedBranchVerdictGateTests(unittest.TestCase):
    def test_mathematical_candidate_survives(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["mathematical_candidate_survives"])
        self.assertTrue(payload["results"]["symbolic_kks_period_nonzero"])

    def test_physical_derivation_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["janus_physical_derivation_closed"])
        self.assertFalse(payload["alpha_generated_now"])
        self.assertIn(
            "noncentral_aroundSigma_spin_lift_not_forced",
            payload["blocking_reasons"],
        )


if __name__ == "__main__":
    unittest.main()
