import unittest

from scripts.build_p0_eft_janus_complex_reality_noncentral_spin_lift_search_gate import (
    build_payload,
)


class ComplexRealityNoncentralSpinLiftSearchGateTests(unittest.TestCase):
    def test_search_classifies_candidate_lifts(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["search_complete"])
        self.assertEqual(
            payload["candidate_lifts"]["central_minus_identity"]["projects_to_CP1"],
            "identity",
        )
        self.assertIn("noncentral_pi_rotation", payload["candidate_lifts"])

    def test_noncentral_lift_is_not_derived(self):
        payload = build_payload()

        self.assertFalse(payload["noncentral_spin_lift_derived"])
        self.assertIn("noncentral_lift_forced_by_geometry", payload["still_missing"])
        self.assertEqual(payload["next_gate"], "ComplexRealityCombinedBranchVerdictGate")


if __name__ == "__main__":
    unittest.main()
