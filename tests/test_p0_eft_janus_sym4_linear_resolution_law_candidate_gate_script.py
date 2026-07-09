import unittest

from janus_lab.janus_phase_space_occupation_search import (
    sym4_linear_resolution_law_candidate_payload,
)


class JanusSym4LinearResolutionLawCandidateGateTests(unittest.TestCase):
    def test_candidate_would_reach_predrag_if_accepted(self):
        payload = sym4_linear_resolution_law_candidate_payload()

        self.assertEqual(payload["inputs"]["N_from_Sym4_C11"], 1001)
        self.assertAlmostEqual(payload["if_accepted"]["a_min"], 1.0 / 1001.0)
        self.assertEqual(payload["if_accepted"]["z_max"], 1000.0)
        self.assertTrue(payload["if_accepted"]["pre_drag_reach"])

    def test_normal_channel_operator_is_still_missing(self):
        payload = sym4_linear_resolution_law_candidate_payload()

        self.assertFalse(payload["why_not_derived"]["normal_channel_spectral_operator_defined"])
        self.assertFalse(payload["why_not_derived"]["a_min_equals_inverse_state_count_proved"])


if __name__ == "__main__":
    unittest.main()
