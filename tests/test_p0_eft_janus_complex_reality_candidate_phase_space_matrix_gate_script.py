import unittest

from scripts.build_p0_eft_janus_complex_reality_candidate_phase_space_matrix_gate import (
    build_payload,
)


class ComplexRealityCandidatePhaseSpaceMatrixGateTests(unittest.TestCase):
    def test_three_core_candidates(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["core_candidate_count"], 3)
        ids = {item["id"] for item in payload["core_candidates"]}
        self.assertIn("active_throat_S2", ids)
        self.assertIn("CP1_spinor_frame_orbit", ids)
        self.assertIn("aroundSigma_cross_compact_phase", ids)

    def test_extensions_have_policy(self):
        payload = build_payload()

        self.assertTrue(payload["matrix_ready"])
        self.assertFalse(payload["alpha_generated_now"])
        self.assertIn("moebius_twisted_throat", {item["id"] for item in payload["extensions"]})
        self.assertIn("compact phase paired with aroundSigma", payload["extension_policy"])


if __name__ == "__main__":
    unittest.main()
