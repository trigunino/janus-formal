import unittest

from scripts.build_p0_eft_janus_complex_reality_cp1_from_janus_pt_gate import (
    build_payload,
)


class ComplexRealityCP1FromJanusPTGateTests(unittest.TestCase):
    def test_cp1_candidate_is_constructed_locally(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["cp1_mathematical_candidate_ready"])
        self.assertEqual(payload["construction"]["fiber"], "P(C^2) = CP1 ~= S2")

    def test_cp1_is_not_yet_janus_pt_derived(self):
        payload = build_payload()

        self.assertFalse(payload["cp1_derived_from_Janus_PT"])
        self.assertIn("global_Z2Sigma_spinor_projection_ready", payload["still_missing"])


if __name__ == "__main__":
    unittest.main()
