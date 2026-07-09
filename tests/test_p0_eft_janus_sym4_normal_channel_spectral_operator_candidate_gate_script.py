import unittest

from janus_lab.janus_phase_space_occupation_search import (
    sym4_normal_channel_spectral_operator_candidate_payload,
)


class JanusSym4NormalChannelSpectralOperatorCandidateGateTests(unittest.TestCase):
    def test_operator_supports_linear_counting_but_not_finite_n(self):
        payload = sym4_normal_channel_spectral_operator_candidate_payload()

        self.assertEqual(payload["inputs"]["N_from_Sym4_C11"], 1001)
        self.assertTrue(payload["operator_attempt"]["linear_mode_indexing_available"])
        self.assertTrue(payload["operator_attempt"]["spectrum_infinite_without_cutoff"])
        self.assertFalse(payload["operator_attempt"]["finite_N_selected_by_operator_alone"])

    def test_if_closed_it_reaches_predrag(self):
        payload = sym4_normal_channel_spectral_operator_candidate_payload()

        self.assertAlmostEqual(payload["if_all_open_steps_are_derived"]["a_min"], 1.0 / 1001.0)
        self.assertEqual(payload["if_all_open_steps_are_derived"]["z_max"], 1000.0)
        self.assertTrue(payload["if_all_open_steps_are_derived"]["pre_drag_reach"])
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
