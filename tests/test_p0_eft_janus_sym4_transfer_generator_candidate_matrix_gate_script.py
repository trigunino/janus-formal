import unittest

from janus_lab.janus_phase_space_occupation_search import (
    sym4_transfer_generator_candidate_matrix_payload,
)


class JanusSym4TransferGeneratorCandidateMatrixGateTests(unittest.TestCase):
    def test_no_anchored_generator_orders_sym4_now(self):
        payload = sym4_transfer_generator_candidate_matrix_payload()

        self.assertEqual(payload["inputs"]["Hilbert_dimension"], 1001)
        self.assertFalse(payload["any_non_rustine_closer"])
        self.assertEqual(payload["non_rustine_closers"], [])

    def test_path_graph_is_not_anchored(self):
        payload = sym4_transfer_generator_candidate_matrix_payload()
        path = next(row for row in payload["candidates"] if row["name"] == "basis_path_graph_transfer")

        self.assertTrue(path["orders_normal_redshift_states"])
        self.assertFalse(path["anchored"])
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
