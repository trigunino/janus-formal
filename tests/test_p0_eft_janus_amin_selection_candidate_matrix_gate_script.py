import unittest

from janus_lab.janus_phase_space_occupation_search import amin_selection_candidate_matrix_payload


class JanusAminSelectionCandidateMatrixGateTests(unittest.TestCase):
    def test_no_current_selector_closes_amin(self):
        payload = amin_selection_candidate_matrix_payload()
        statuses = {row["name"]: row["status"] for row in payload["candidates"]}

        self.assertEqual(statuses["drag_reach_definition"], "circular")
        self.assertEqual(statuses["Eq40_length_unit_ratio"], "underdetermined")
        self.assertEqual(statuses["published_late_SN_throat"], "fails_predrag")

    def test_topological_integer_is_open_not_closed(self):
        payload = amin_selection_candidate_matrix_payload()
        statuses = {row["name"]: row["status"] for row in payload["candidates"]}

        self.assertEqual(statuses["topological_integer_sector"], "open_if_N_derived")


if __name__ == "__main__":
    unittest.main()
