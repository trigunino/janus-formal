import unittest

from scripts.build_p0_eft_janus_complex_reality_quantum_candidate_workbench_gate import (
    build_payload,
)


class ComplexRealityQuantumCandidateWorkbenchGateTests(unittest.TestCase):
    def test_candidates_are_projected_into_quantum_workbench(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["source_matrix_ready"])
        self.assertEqual(payload["best_current_quantum_candidate"], "CP1_spinor_frame_orbit")
        self.assertIn("active_throat_S2", payload["workbench"])
        self.assertIn("aroundSigma_cross_compact_phase", payload["workbench"])

    def test_no_candidate_is_alpha_ready(self):
        payload = build_payload()

        self.assertFalse(payload["any_candidate_alpha_ready"])
        self.assertIn(
            "map_j_to_alpha_m",
            payload["workbench"]["CP1_spinor_frame_orbit"]["blocked_by"],
        )


if __name__ == "__main__":
    unittest.main()
