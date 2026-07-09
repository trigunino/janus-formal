import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    two_cosh_branch_matching_obstruction_payload,
)


class JanusTwoCoshBranchMatchingObstructionGateTests(unittest.TestCase):
    def test_two_cosh_match_at_late_throat_is_not_c1(self):
        payload = two_cosh_branch_matching_obstruction_payload()
        match = payload["matching_at_late_throat"]
        self.assertTrue(match["C0_scale_factor_match_possible"])
        self.assertFalse(match["C1_shape_match_possible_without_extra_lapse_or_surface"])
        self.assertGreater(match["early_shape_H_over_du"], 0.0)
        self.assertEqual(match["late_shape_H_over_du"], 0.0)

    def test_requires_real_transition_law(self):
        payload = two_cosh_branch_matching_obstruction_payload()
        routes = " ".join(payload["non_rustine_escape_routes"])
        self.assertIn("transition surface", routes)
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
