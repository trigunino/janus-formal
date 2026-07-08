import unittest

from scripts.build_p0_eft_janus_complex_reality_candidate_boundary_phase_space_gate import (
    build_payload,
)


class ComplexRealityCandidateBoundaryPhaseSpaceGateTests(unittest.TestCase):
    def test_candidate_constructs_closed_two_cycle(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["candidate_boundary_phase_space_constructed"])
        self.assertEqual(
            payload["candidate"]["phase_space"]["closed_two_cycle"],
            "CP1",
        )
        self.assertEqual(
            payload["candidate"]["phase_space"]["period"],
            "Integral_CP1 Omega_j = 4*pi*j",
        )

    def test_candidate_is_not_yet_physical_alpha_law(self):
        payload = build_payload()

        self.assertFalse(payload["candidate_boundary_phase_space_physically_accepted"])
        self.assertFalse(payload["alpha_generated_now"])
        self.assertIn(
            "that j maps to alpha_m",
            payload["what_this_does_not_prove"],
        )


if __name__ == "__main__":
    unittest.main()
