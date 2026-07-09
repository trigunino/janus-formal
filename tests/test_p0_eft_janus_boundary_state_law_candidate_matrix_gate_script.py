import unittest

from janus_lab.janus_phase_space_occupation_search import (
    boundary_state_law_candidate_matrix_payload,
)


class JanusBoundaryStateLawCandidateMatrixGateTests(unittest.TestCase):
    def test_number_theory_candidates_are_recorded(self):
        payload = boundary_state_law_candidate_matrix_payload()

        self.assertEqual(payload["required_N"], 1001)
        self.assertEqual(payload["number_theory"]["factorization"], "1001 = 7 * 11 * 13")
        self.assertTrue(payload["number_theory"]["exterior_power_candidate_matches"])
        self.assertTrue(payload["number_theory"]["current_janus_source_anchor_for_14_modes"])
        self.assertEqual(payload["number_theory"]["M31_janus_lie_dimension"], 11)
        self.assertEqual(payload["number_theory"]["M31_independent_CPT_generators"], 3)
        self.assertEqual(payload["number_theory"]["M31_spacetime_translation_dimension"], 4)
        self.assertTrue(payload["number_theory"]["current_janus_source_anchor_for_degree_4"])
        self.assertTrue(payload["number_theory"]["symmetric_power_C11_candidate_matches"])
        self.assertEqual(
            payload["current_acceptance"]["best_current_candidate"],
            "symmetric_power_boundary_boson_sector",
        )

    def test_symmetric_power_candidate_is_explicit(self):
        payload = boundary_state_law_candidate_matrix_payload()
        sym = next(
            row for row in payload["candidates"] if row["name"] == "symmetric_power_boundary_boson_sector"
        )

        self.assertIn("C(11+4-1,4)=C(14,4)=1001", sym["target_match"])
        self.assertIn("degree-4", sym["missing"])

    def test_no_candidate_is_accepted_as_derived(self):
        payload = boundary_state_law_candidate_matrix_payload()

        self.assertEqual(payload["current_acceptance"]["accepted_as_no_fit_law"], [])
        self.assertTrue(payload["current_acceptance"]["requires_new_boundary_state_law"])
        self.assertTrue(
            all(not row["derived_from_current_janus"] for row in payload["candidates"])
        )

    def test_exterior_power_candidate_is_explicit(self):
        payload = boundary_state_law_candidate_matrix_payload()
        exterior = next(
            row for row in payload["candidates"] if row["name"] == "exterior_power_boundary_fermion_sector"
        )

        self.assertIn("C(14,4)=1001", exterior["target_match"])
        self.assertIn("Lambda^4 sector", exterior["missing"])


if __name__ == "__main__":
    unittest.main()
