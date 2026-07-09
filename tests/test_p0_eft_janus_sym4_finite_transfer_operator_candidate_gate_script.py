import unittest

from janus_lab.janus_phase_space_occupation_search import (
    sym4_finite_transfer_operator_candidate_payload,
)


class JanusSym4FiniteTransferOperatorCandidateGateTests(unittest.TestCase):
    def test_finite_n_is_intrinsic_to_sym4_sector(self):
        payload = sym4_finite_transfer_operator_candidate_payload()

        self.assertEqual(payload["inputs"]["Hilbert_sector"], "Sym^4(C^11)")
        self.assertEqual(payload["inputs"]["Hilbert_dimension"], 1001)
        self.assertEqual(payload["what_would_close_if_derived"]["z_max"], 1000.0)

    def test_transfer_generator_is_still_missing(self):
        payload = sym4_finite_transfer_operator_candidate_payload()

        self.assertFalse(payload["operator_requirements"]["finite_transfer_matrix_on_Sym4_defined"])
        self.assertFalse(payload["operator_requirements"]["ordered_normal_resolution_spectrum_derived"])
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
